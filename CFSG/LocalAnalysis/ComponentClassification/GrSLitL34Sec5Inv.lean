module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34Cert
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Four
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Setup

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.PSL3Four.F4

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_zStarIn {C L : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) (hX : ¬ oddIn L ≤ (center ↥L).map L.subtype) :
    L ⊓ centralizer (oddIn L : Set G) ≤ zStarIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L C hLC).mp hL
  have hperf : Group.IsPerfect L := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hL
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLC).toMonoidHom)
      (subgroupOfEquivOfLe hLC).surjective
  set K : Subgroup G := L ⊓ centralizer (oddIn L : Set G) with hK
  have hKL : K ≤ L := inf_le_left
  have hLN : L ≤ normalizer (K : Set G) := by
    intro l hl
    rw [mem_normalizer_iff]
    have hlX : l ∈ normalizer (oddIn L : Set G) :=
      normalizer_le_normalizer_oddIn L (le_normalizer hl)
    intro y
    constructor
    · intro hy
      obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
      refine mem_inf.mpr ⟨mul_mem (mul_mem hl hyL) (inv_mem hl), ?_⟩
      rw [mem_centralizer_iff] at hyC ⊢
      intro x hx
      have hx' : l⁻¹ * x * l ∈ oddIn L := by
        have := (mem_normalizer_iff.mp (inv_mem hlX) x).mp hx
        simpa using this
      have h := hyC _ hx'
      calc x * (l * y * l⁻¹) = l * ((l⁻¹ * x * l) * y) * l⁻¹ := by group
        _ = l * (y * (l⁻¹ * x * l)) * l⁻¹ := by rw [h]
        _ = l * y * l⁻¹ * x := by group
    · intro hy
      obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
      have hyL' : y ∈ L := by
        have := mul_mem (mul_mem (inv_mem hl) hyL) hl
        simpa [mul_assoc] using this
      refine mem_inf.mpr ⟨hyL', ?_⟩
      rw [mem_centralizer_iff] at hyC ⊢
      intro x hx
      have hx' : l * x * l⁻¹ ∈ oddIn L := (mem_normalizer_iff.mp hlX x).mp hx
      have h := hyC _ hx'
      calc x * y = l⁻¹ * ((l * x * l⁻¹) * (l * y * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * y * l⁻¹) * (l * x * l⁻¹)) * l := by rw [h]
        _ = y * x := by group
  have hKn : (K.subgroupOf L).Normal := by
    rw [normal_subgroupOf_iff hKL]
    intro k l hk hl
    exact (mem_normalizer_iff.mp (hLN hl) k).mp hk
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  have hKbar : ((K.subgroupOf L).map π).Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hKbar with h | h
  ·
    exfalso
    have hsup : (pPrimeCore 2 L).map L.subtype ⊔ K = L := by
      apply le_antisymm (sup_le (map_subtype_le _) hKL)
      intro l hl
      have hl' : π ⟨l, hl⟩ ∈ (K.subgroupOf L).map π := h ▸ mem_top _
      obtain ⟨k, hk, hkl⟩ := hl'
      have hko : k⁻¹ * ⟨l, hl⟩ ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.mp hkl
      have h1 : l = (k : G) * ((k⁻¹ * ⟨l, hl⟩ : L) : G) := by simp
      rw [h1]
      exact mul_mem (mem_sup_right (mem_subgroupOf.mp hk)) (mem_sup_left ⟨_, hko, rfl⟩)
    have hKeq := eq_of_pPrimeCore_sup_eq hKL hKn hperf hsup
    apply hX
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    have hgK : (g : G) ∈ K := (le_of_eq hKeq.symm) g.2
    exact ((mem_centralizer_iff.mp (mem_inf.mp hgK).2) _ ⟨x, hx, rfl⟩).symm
  ·
    intro k hk
    have hk' : π ⟨k, hKL hk⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := h ⟨⟨k, hKL hk⟩, hk, rfl⟩
    refine ⟨⟨k, hKL hk⟩, ?_, rfl⟩
    rw [Sol78.fusionZStar_eq_comap]
    exact hk'

theorem conj_eq_inv_of_inf_centralizer_eq_bot {X : Subgroup G} {u : G}
    (huX : u ∈ normalizer (X : Set G)) (hu2 : u * u = 1)
    (h : X ⊓ centralizer ({u} : Set G) = ⊥) : ∀ x ∈ X, u * x * u⁻¹ = x⁻¹ := by
  let φ : X →* X :=
    { toFun := fun x => ⟨u * x * u⁻¹, (mem_normalizer_iff.mp huX x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [coe_mul]; group }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro x hx
    have hx' : u * (x : G) * u⁻¹ = x := congrArg Subtype.val hx
    have hmem : (x : G) ∈ X ⊓ centralizer ({u} : Set G) := by
      refine mem_inf.mpr ⟨x.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x : G) * u = u * x * u⁻¹ * u := by rw [hx']
        _ = u * x := by group
    rw [h] at hmem
    exact Subtype.ext (mem_bot.mp hmem)
  have hinv : Function.Involutive φ := by
    intro x
    ext
    show u * (u * (x : G) * u⁻¹) * u⁻¹ = x
    have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [hu]
    calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu2, one_mul, mul_one]
  have key := hφ.coe_eq_inv_of_involutive hinv
  intro x hx
  have := congrFun key ⟨x, hx⟩
  exact congrArg Subtype.val this

omit [Finite G] in
theorem inv_conj_eq_inv {X : Subgroup G} {a : G} (haX : a ∈ normalizer (X : Set G))
    (h : ∀ y ∈ X, a * y * a⁻¹ = y⁻¹) : ∀ y ∈ X, a⁻¹ * y * a = y⁻¹ := by
  intro y hy
  have hz : a⁻¹ * y * a ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem haX) y).mp hy
    simpa using this
  have h1 := h _ hz
  have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
  rw [e] at h1
  exact inv_eq_iff_eq_inv.mp h1.symm

theorem mem_coreActionKernel_of_inverts {C L : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) (hX : ¬ oddIn L ≤ (center ↥L).map L.subtype)
    {u : G} (huN : u ∈ normalizer (L : Set G)) (hinv : ∀ x ∈ oddIn L, u * x * u⁻¹ = x⁻¹) :
    u ∈ coreActionKernel L := by
  have hperf : Group.IsPerfect L := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hL
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLC).toMonoidHom)
      (subgroupOfEquivOfLe hLC).surjective
  have huX : u ∈ normalizer (oddIn L : Set G) := normalizer_le_normalizer_oddIn L huN
  have hcomm : ∀ n ∈ L, n * u * n⁻¹ * u⁻¹ ∈ L ⊓ centralizer (oddIn L : Set G) := by
    intro n hn
    have hnX : n ∈ normalizer (oddIn L : Set G) :=
      normalizer_le_normalizer_oddIn L (le_normalizer hn)
    set a := n * u * n⁻¹ with ha
    have haX : a ∈ normalizer (oddIn L : Set G) :=
      mul_mem (mul_mem hnX huX) (inv_mem hnX)
    have hainv : ∀ y ∈ oddIn L, a * y * a⁻¹ = y⁻¹ := by
      intro y hy
      have hy' : n⁻¹ * y * n ∈ oddIn L := by
        have := (mem_normalizer_iff.mp (inv_mem hnX) y).mp hy
        simpa using this
      have h := hinv _ hy'
      calc a * y * a⁻¹ = n * (u * (n⁻¹ * y * n) * u⁻¹) * n⁻¹ := by rw [ha]; group
        _ = n * (n⁻¹ * y * n)⁻¹ * n⁻¹ := by rw [h]
        _ = y⁻¹ := by group
    have hainv' := inv_conj_eq_inv haX hainv
    refine mem_inf.mpr ⟨?_, mem_centralizer_iff.mpr fun x hx => ?_⟩
    · have h1 : u * n⁻¹ * u⁻¹ ∈ L := (mem_normalizer_iff.mp huN _).mp (inv_mem hn)
      rw [show n * u * n⁻¹ * u⁻¹ = n * (u * n⁻¹ * u⁻¹) by group]
      exact mul_mem hn h1
    · have h1 : (a * u⁻¹)⁻¹ * x * (a * u⁻¹) = x := by
        calc (a * u⁻¹)⁻¹ * x * (a * u⁻¹) = u * (a⁻¹ * x * a) * u⁻¹ := by group
          _ = u * x⁻¹ * u⁻¹ := by rw [hainv' x hx]
          _ = x := by rw [hinv _ (inv_mem hx), inv_inv]
      calc x * (a * u⁻¹) = (a * u⁻¹) * ((a * u⁻¹)⁻¹ * x * (a * u⁻¹)) := by group
        _ = (a * u⁻¹) * x := by rw [h1]
  have hZ : ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ (Open.fusionZStar L).map L.subtype := by
    intro l hl
    have h := inf_centralizer_le_zStarIn hLC hL hX (hcomm l hl)
    have e : u * l * u⁻¹ * l⁻¹ = (l * u * l⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h
  have hO := commutator_mem_oddCore_of_mem_fusionZStar hperf huN hZ
  refine mem_coreActionKernel.mpr ⟨huN, fun j hj => ?_⟩
  have h1 := hO j⁻¹ (inv_mem hj)
  have h2 := (mem_normalizer_iff.mp (normalizer_le_normalizer_oddIn L (inv_mem huN)) _).mp h1
  have e : u⁻¹ * (u * j⁻¹ * u⁻¹ * j⁻¹⁻¹) * u⁻¹⁻¹ = j⁻¹ * u⁻¹ * j * u := by group
  rw [e] at h2
  exact h2

theorem exists_quotient_psl34 {L : Subgroup G} (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) :
    ∃ π : (↥L ⧸ pPrimeCore 2 ↥L) →* PSL3Four.S, Function.Surjective π ∧
      π.ker = center (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := nonempty_quotient_center_equiv_fusionZStar ↥L
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
  set π : (↥L ⧸ pPrimeCore 2 ↥L) →* PSL3Four.S :=
    (e₁.trans ψ).toMonoidHom.comp (QuotientGroup.mk' (center _)) with hπdef
  have hkerπ : π.ker = center (↥L ⧸ pPrimeCore 2 ↥L) := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨π, (e₁.trans ψ).surjective.comp (QuotientGroup.mk'_surjective _), hkerπ, ?_⟩
  intro z hz hz3
  rw [hkerπ] at hz
  have hn : (zpowers z).Normal := ⟨fun n hn g => by
    have hc : g * n = n * g := (mem_center_iff.mp (Subgroup.zpowers_le.mpr hz hn)) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (zpowers z)) := by
    rw [Nat.card_zpowers]
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h1 <;> rw [h1] <;>
      norm_num
  have hbot := (pPrimeCore_eq_bot_iff.mp (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2)) _ hn hcop
  exact (zpowers_eq_bot).mp hbot

theorem exists_commuting_involution {L : Subgroup G} (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L))
    {l : G} (hl : l ∈ L) (hl2 : l * l = 1) (hlZ : l ∉ zStarIn L) :
    ∃ w ∈ L, w * w = 1 ∧ w * l = l * w ∧ w ∉ zStarIn L ∧ l⁻¹ * w ∉ zStarIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker, h3⟩ := exists_quotient_psl34 h
  have hK : π.ker ≤ center (↥L ⧸ pPrimeCore 2 ↥L) := hker.le
  set f := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hf
  set ψ : ↥L →* PSL3Four.S := π.comp f with hψ
  have hψsurj : Function.Surjective ψ := hπ.comp (QuotientGroup.mk'_surjective _)
  have hψZ : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ zStarIn L := by
    intro x
    rw [hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rw [Sol78.fusionZStar_eq_comap]
      exact hx
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      subst this
      rw [Sol78.fusionZStar_eq_comap] at hx'
      exact hx'
  set l' : ↥L := ⟨l, hl⟩ with hl'
  have hψl1 : ψ l' ≠ 1 := fun h1 => hlZ ((hψZ l').mp h1)
  have hl'2 : l' * l' = 1 := Subtype.ext hl2
  have hψl2 : ψ l' * ψ l' = 1 := by rw [← map_mul, hl'2, map_one]
  set t₀ : PSL3Four.S := rhoS (x01S 1) with ht₀
  have ht₀2 : t₀ * t₀ = 1 := by rw [ht₀, rhoS_x01_mul, CharTwo.add_self_eq_zero, rhoS_x01_zero]
  have ht₀1 : t₀ ≠ 1 := rhoS_x01_ne_one (by decide)
  obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (S_le_R t₀.2) (S_le_R (ψ l').2)
    (congrArg Subtype.val ht₀2) (congrArg Subtype.val hψl2)
    (fun h1 => ht₀1 (Subtype.ext h1)) (fun h1 => hψl1 (Subtype.ext h1))
    (mul_mem (inv_mem t₀.2) (ψ l').2)
  set s : PSL3Four.S := ⟨y, hyS⟩ with hs
  have hsl : s * t₀ * s⁻¹ = ψ l' := Subtype.ext hy
  obtain ⟨g, hg⟩ := hψsurj s
  set m : ↥L := g⁻¹ * l' * g with hm
  have hψm : ψ m = t₀ := by
    rw [hm, map_mul, map_mul, map_inv, hg, ← hsl]
    group
  have hm2 : m * m = 1 := by
    rw [hm]
    calc g⁻¹ * l' * g * (g⁻¹ * l' * g) = g⁻¹ * (l' * l') * g := by group
      _ = 1 := by rw [hl'2]; group
  obtain ⟨Y, hYK, hYV, hYab⟩ := exists_split hπ hK h3 rootX01_commutators
    (h := rhoS hS) (fun v hv => by
      obtain ⟨c, rfl⟩ := mem_rootX01.mp hv
      rw [rootX01_conj_h]
      exact ⟨_, rfl⟩) rootX01_norm
  have hab := comap_comm_of_commutators hπ hK rootX01_commutators
  have hYX : Y ≤ rootX01.comap π := by
    rw [← map_le_iff_le_comap, hYV]
  obtain ⟨y₂, hy₂, hπy₂⟩ : ∃ y₂ ∈ Y, π y₂ = rhoS (x01S ω) := by
    have : rhoS (x01S ω) ∈ Y.map π := hYV ▸ mem_rootX01.mpr ⟨ω, rfl⟩
    obtain ⟨y₂, hy₂, h⟩ := this
    exact ⟨y₂, hy₂, h⟩
  have hy₂2 : y₂ * y₂ = 1 := by
    have hm' : y₂ * y₂ ∈ Y ⊓ π.ker := Subgroup.mem_inf.mpr ⟨mul_mem hy₂ hy₂, by
      rw [MonoidHom.mem_ker, map_mul, hπy₂, rhoS_x01_mul, CharTwo.add_self_eq_zero, rhoS_x01_zero]⟩
    rw [hYK] at hm'
    exact mem_bot.mp hm'
  have hfm : f m ∈ rootX01.comap π := by
    rw [mem_comap]
    have : π (f m) = t₀ := hψm
    rw [this, ht₀]
    exact mem_rootX01.mpr ⟨1, rfl⟩
  have hcomm : y₂ * f m = f m * y₂ := hab _ (hYX hy₂) _ hfm
  have hodd : ¬ 2 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    intro hd
    exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
      (even_iff_two_dvd.mpr hd)
  have hm1 : m ≠ 1 := by
    rintro h1
    apply ht₀1
    rw [← hψm, h1, map_one]
  have hm2' : IsPGroup 2 (zpowers m) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two, hm2]) hm1
  have hcen := map_centralizer_eq_of_odd_ker f (QuotientGroup.mk'_surjective _) hodd hm2'
  have hy₂mem : y₂ ∈ (centralizer (zpowers m : Set ↥L)).map f := by
    rw [hcen, MonoidHom.map_zpowers, mem_centralizer_iff]
    intro g' hg'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg'
    exact (Commute.zpow_left hcomm.symm i).eq
  obtain ⟨w', hw'c, hw'2, hfw'⟩ := exists_involution_lift _ hy₂mem hy₂2
  have hw'm : w' * m = m * w' := (mem_centralizer_iff.mp hw'c m (mem_zpowers m)).symm
  set w : ↥L := g * w' * g⁻¹ with hw
  have hψw : ψ w = s * rhoS (x01S ω) * s⁻¹ := by
    have : ψ w' = rhoS (x01S ω) := by
      show π (f w') = _
      rw [hfw', hπy₂]
    rw [hw, map_mul, map_mul, map_inv, hg, this]
  refine ⟨(w : G), w.2, ?_, ?_, ?_, ?_⟩
  · have : w * w = 1 := by
      rw [hw]
      calc g * w' * g⁻¹ * (g * w' * g⁻¹) = g * (w' * w') * g⁻¹ := by group
        _ = 1 := by rw [hw'2]; group
    exact congrArg Subtype.val this
  · have : w * l' = l' * w := by
      have hl'm : l' = g * m * g⁻¹ := by rw [hm]; group
      rw [hl'm, hw]
      calc g * w' * g⁻¹ * (g * m * g⁻¹) = g * (w' * m) * g⁻¹ := by group
        _ = g * (m * w') * g⁻¹ := by rw [hw'm]
        _ = g * m * g⁻¹ * (g * w' * g⁻¹) := by group
    exact congrArg Subtype.val this
  · intro hwZ
    have h1 := (hψZ w).mpr hwZ
    rw [hψw] at h1
    have h2 : rhoS (x01S ω) = 1 := by
      calc rhoS (x01S ω) = s⁻¹ * (s * rhoS (x01S ω) * s⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    exact rhoS_x01_ne_one (by decide) h2
  · intro hwZ
    have hlw : (l⁻¹ * (w : G)) = ((l'⁻¹ * w : ↥L) : G) := rfl
    rw [hlw] at hwZ
    have h1 := (hψZ _).mpr hwZ
    rw [map_mul, map_inv, ← hsl, hψw] at h1
    have h2 : t₀⁻¹ * rhoS (x01S ω) = 1 := by
      calc t₀⁻¹ * rhoS (x01S ω) = s⁻¹ * ((s * t₀ * s⁻¹)⁻¹ * (s * rhoS (x01S ω) * s⁻¹)) * s := by
            group
        _ = 1 := by rw [h1]; group
    have h3 : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
    rw [h3, ht₀, rhoS_x01_mul] at h2
    exact rhoS_x01_ne_one (by decide) h2

end CFSG.ComponentClassification.GrSLit.GrS5
