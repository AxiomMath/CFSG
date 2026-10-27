module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Odd

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_mul_card {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := Subgroup.index_mul_card (H.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1

theorem exists_conj_of_sylow {K A B : Subgroup G} (hA2 : IsPGroup 2 A)
    (hB2 : IsPGroup 2 B) (hAi : ¬ 2 ∣ A.relIndex K) (hBi : ¬ 2 ∣ B.relIndex K) :
    ∃ m ∈ K, ∀ x : G, x ∈ K → (x ∈ B ↔ m⁻¹ * x * m ∈ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SA : Sylow 2 K := (hA2.comap_subtype (K := K)).toSylow hAi
  let SB : Sylow 2 K := (hB2.comap_subtype (K := K)).toSylow hBi
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K SA SB
  refine ⟨m, m.2, fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : K) ∈ (SB : Subgroup K) ↔
      (⟨x, hx⟩ : K) ∈ ((m • SA : Sylow 2 K) : Subgroup K) := by
    rw [hm]
  have h2 : (⟨x, hx⟩ : K) ∈ ((m • SA : Sylow 2 K) : Subgroup K) ↔
      m⁻¹ * ⟨x, hx⟩ * m ∈ (SA : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have h3 : (⟨x, hx⟩ : K) ∈ (SB : Subgroup K) ↔ x ∈ B := Iff.rfl
  have h4 : m⁻¹ * ⟨x, hx⟩ * m ∈ (SA : Subgroup K) ↔ (m : G)⁻¹ * x * m ∈ A := Iff.rfl
  rw [← h3, h1, h2, h4]

theorem exists_sylow_fusion {t z : G} (hc : ∃ g : G, z = g * t * g⁻¹)
    (hodd : Odd ((centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)).relIndex
      (centralizer ({t} : Set G)))) {a : G}
    (ha : a ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
    (ha2 : IsPGroup 2 (zpowers a)) :
    ∃ S₀ : Subgroup G, a ∈ S₀ ∧ S₀ ≤ centralizer ({t} : Set G) ∧ S₀ ≤ centralizer ({z} : Set G) ∧
      IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.relIndex (centralizer ({t} : Set G)) ∧
      ∃ n : G, (∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀) ∧ n * t * n⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := hc
  set N : Subgroup G := centralizer ({t} : Set G) with hN
  set C₀ : Subgroup G := centralizer ({z} : Set G) ⊓ N with hC₀
  have hC₀N : C₀ ≤ N := inf_le_right
  have hP' : IsPGroup 2 ((zpowers a).subgroupOf C₀) := ha2.comap_subtype
  obtain ⟨P₀, hP'P₀⟩ := hP'.exists_le_sylow
  set S₀ : Subgroup G := (P₀ : Subgroup C₀).map C₀.subtype with hS₀
  have hS₀C : S₀ ≤ C₀ := Subgroup.map_subtype_le _
  have hS₀2 : IsPGroup 2 S₀ := P₀.isPGroup'.map C₀.subtype
  have hS₀card : Nat.card S₀ = Nat.card (P₀ : Subgroup C₀) :=
    Subgroup.card_map_of_injective C₀.subtype_injective
  have hS₀rel : ¬ 2 ∣ S₀.relIndex N := by
    have h1 := Subgroup.relIndex_mul_relIndex S₀ C₀ N hS₀C hC₀N
    have h2 : S₀.relIndex C₀ = (P₀ : Subgroup C₀).index := by
      show (S₀.subgroupOf C₀).index = _
      rw [hS₀]
      exact congrArg Subgroup.index (Subgroup.comap_map_eq_self_of_injective C₀.subtype_injective _)
    have h3 : ¬ 2 ∣ (P₀ : Subgroup C₀).index := P₀.not_dvd_index
    rw [← h1, h2]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact h3 h
    · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  set T : Subgroup G := S₀.map (MulAut.conj g⁻¹).toMonoidHom with hT
  have hS₀z : S₀ ≤ centralizer ({z} : Set G) := hS₀C.trans inf_le_left
  have hS₀N : S₀ ≤ N := hS₀C.trans hC₀N
  have hTN : T ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    have hxz := mem_centralizer_singleton_iff.1 (hS₀z hx)
    rw [hN, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hg] at hxz
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxz]
      _ = t * (g⁻¹ * x * g) := by group
  have hT2 : IsPGroup 2 T := hS₀2.map _
  have hTcard : Nat.card T = Nat.card S₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hTrel : ¬ 2 ∣ T.relIndex N := by
    have h1 := relIndex_mul_card hTN
    have h2 := relIndex_mul_card hS₀N
    have hpos : 0 < Nat.card S₀ := Nat.card_pos
    have : T.relIndex N = S₀.relIndex N := by
      rw [hTcard] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    rw [this]; exact hS₀rel
  obtain ⟨m, hmN, hm⟩ := exists_conj_of_sylow (K := N) (A := T) (B := S₀) hT2 hS₀2 hTrel hS₀rel
  have haS₀ : a ∈ S₀ := ⟨⟨a, ha⟩, hP'P₀ (mem_zpowers a), rfl⟩
  refine ⟨S₀, haS₀, hS₀N, hS₀z, hS₀2, hS₀rel, g * m⁻¹, fun x => ?_, ?_⟩
  · have hmem : ∀ y : G, y ∈ T ↔ g * y * g⁻¹ ∈ S₀ := by
      intro y
      constructor
      · rintro ⟨x', hx', rfl⟩
        have : g * ((MulAut.conj g⁻¹).toMonoidHom x') * g⁻¹ = x' := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group
        rw [this]; exact hx'
      · intro hy
        exact ⟨g * y * g⁻¹, hy, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩
    have e1 : g * (m⁻¹ * x * m) * g⁻¹ = g * m⁻¹ * x * (g * m⁻¹)⁻¹ := by group
    have e2 : m⁻¹ * x * m = g⁻¹ * (g * m⁻¹ * x * (g * m⁻¹)⁻¹) * g := by group
    constructor
    · intro hx
      have h1 := (hm x (hS₀N hx)).1 hx
      have := (hmem _).1 h1
      rwa [e1] at this
    · intro hy
      have hT' : m⁻¹ * x * m ∈ T := by
        rw [e2]
        exact (hmem _).2 (by simpa [mul_assoc] using hy)
      have hxN : x ∈ N := by
        have h3 : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
        rw [← h3]
        exact N.mul_mem (N.mul_mem hmN (hTN hT')) (N.inv_mem hmN)
      exact (hm x hxN).2 hT'
  · have hmc : m * t = t * m := mem_centralizer_singleton_iff.1 hmN
    rw [hg]
    calc g * m⁻¹ * t * (g * m⁻¹)⁻¹ = g * (m⁻¹ * t * m) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by
        congr 2
        calc m⁻¹ * t * m = m⁻¹ * (t * m) * 1 := by group
          _ = t := by rw [← hmc]; group

variable {L : Subgroup G} {f : G}

namespace FourHyp

theorem odd_relIndex_centralizer (H : FourHyp G L f) (hcl : ClassFacts L) {s : G}
    (hs : IsTight L s) (hn : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹)
    (hc : ∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹) :
    Odd ((centralizer ({s ^ 2} : Set G) ⊓ normalizer (L : Set G)).relIndex
      (normalizer (L : Set G))) := by
  obtain ⟨u, hu, huu, hucen, hubar, hφ2, hφfix⟩ := H.tight_u hs
  obtain ⟨hα, hodd⟩ := hcl _ hubar ⟨_, hφ2, hφfix⟩
  obtain ⟨h₀, hh₀⟩ := hc
  have hf4 : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact H.pow_four
  set N : Subgroup G := normalizer (L : Set G) with hN
  let _ : MulAction N (L ⧸ center L) := MulAction.compHom (L ⧸ center L) (normalizerAction L)
  have hact : ∀ n : N, ∃ l : L, (l : G) = (n : G) * (u : G) * (n : G)⁻¹ ∧
      n • (u : L ⧸ center L) = (l : L ⧸ center L) := by
    intro n
    have hy : (n : G) * (u : G) * (n : G)⁻¹ ∈ L := (mem_normalizer_iff.1 n.2 (u : G)).1 u.2
    exact ⟨⟨_, hy⟩, rfl, normalizerAction_apply n u ⟨_, hy⟩ rfl⟩
  have hstab : MulAction.stabilizer N (u : L ⧸ center L) =
      (centralizer ({s ^ 2} : Set G) ⊓ N).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro h
      obtain ⟨l, hl, hl'⟩ := hact n
      rw [hl'] at h
      have hk : l⁻¹ * u ∈ center L := (QuotientGroup.eq).1 h
      have hkG : ((l⁻¹ * u : L) : G) ∈ (center L).map L.subtype := ⟨_, hk, rfl⟩
      rw [map_center_eq_inf_centralizer] at hkG
      rcases H.eq_one_or_eq_sq_of_mem hkG.1 hkG.2 with h1 | h1
      · refine ⟨?_, n.2⟩
        have h2 : (l : G) = (u : G) := by
          have : (l : G)⁻¹ * (u : G) = 1 := by simpa using h1
          exact (inv_mul_eq_one.1 this)
        have h3 : (n : G) * (u : G) * (n : G)⁻¹ = (u : G) := by rw [← hl, h2]
        rw [← hu]
        calc (n : G) * (u : G) = ((n : G) * (u : G) * (n : G)⁻¹) * (n : G) := by group
          _ = (u : G) * (n : G) := by rw [h3]
      · exfalso
        apply hn
        have h2 : (l : G)⁻¹ * (u : G) = f ^ 2 := by simpa using h1
        have h3 : (u : G) * f ^ 2 = (n : G) * (u : G) * (n : G)⁻¹ := by
          rw [← hl]
          have : (u : G) = (l : G) * f ^ 2 := by rw [← h2]; group
          calc (u : G) * f ^ 2 = (l : G) * (f ^ 2 * f ^ 2) := by rw [this]; group
            _ = (l : G) := by rw [hf4, mul_one]
        refine ⟨(n : G) * h₀, ?_⟩
        rw [← hu] at hh₀
        rw [← hu, h3, hh₀]
        group
    · rintro ⟨h, -⟩
      obtain ⟨l, hl, hl'⟩ := hact n
      have h3 : (n : G) * (u : G) * (n : G)⁻¹ = (u : G) := by
        have : (n : G) * s ^ 2 = s ^ 2 * (n : G) := h
        rw [← hu] at this
        calc (n : G) * (u : G) * (n : G)⁻¹ = ((u : G) * (n : G)) * (n : G)⁻¹ := by rw [this]
          _ = (u : G) := by group
      have : l = u := Subtype.ext (by rw [hl, h3])
      rw [hl', this]
  have horb : MulAction.orbit N (u : L ⧸ center L) =
      MulAction.orbit (ConjAct (L ⧸ center L)) (u : L ⧸ center L) := by
    ext w
    rw [MulAction.mem_orbit_iff, ConjAct.mem_orbit_conjAct, isConj_iff]
    constructor
    · rintro ⟨n, rfl⟩
      obtain ⟨q, hq⟩ := hα (normalizerAction L n)
      exact ⟨q⁻¹, by
        change q⁻¹ * (normalizerAction L n (u : L ⧸ center L)) * q⁻¹⁻¹ = _
        rw [hq]; group⟩
    · rintro ⟨c, hc⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective c⁻¹
      have hlN : (l : G) ∈ N := by
        rw [hN, mem_normalizer_iff]
        intro y
        constructor
        · intro hy; exact L.mul_mem (L.mul_mem l.2 hy) (L.inv_mem l.2)
        · intro hy
          have := L.mul_mem (L.mul_mem (L.inv_mem l.2) hy) l.2
          simpa [mul_assoc] using this
      obtain ⟨l', hl'1, hl'2⟩ := hact ⟨l, hlN⟩
      refine ⟨⟨l, hlN⟩, ?_⟩
      rw [hl'2]
      have : (l' : L) = l * u * l⁻¹ := Subtype.ext (by simpa using hl'1)
      rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl, inv_inv]
      calc c⁻¹ * (u : L ⧸ center L) * c = c⁻¹ * (c * w * c⁻¹) * c := by rw [hc]
        _ = w := by group
  have h1 := MulAction.index_stabilizer N (u : L ⧸ center L)
  have h2 := MulAction.index_stabilizer (ConjAct (L ⧸ center L)) (u : L ⧸ center L)
  have h3 : (centralizer ({(u : L ⧸ center L)} : Set (L ⧸ center L))).index =
      (MulAction.stabilizer (ConjAct (L ⧸ center L)) (u : L ⧸ center L)).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Subgroup.index_comap_of_surjective _ (ConjAct.toConjAct.surjective)
  have h4 : (centralizer ({s ^ 2} : Set G) ⊓ N).relIndex N =
      (MulAction.stabilizer N (u : L ⧸ center L)).index := by
    rw [hstab]; rfl
  rw [h4, h1, horb, ← h2, ← h3]
  exact hodd

end FourHyp

end CFSG.EvenSporadicStandard.TwoHS
