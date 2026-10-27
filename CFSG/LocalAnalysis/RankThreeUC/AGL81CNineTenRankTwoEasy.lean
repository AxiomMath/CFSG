module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoCent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoChar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoSL
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoInv
import CFSG.LocalAnalysis.SteinbergBVCcommSupercriticalShape
import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem isHomocyclicRank2_centralizer (hp : p.Prime) {A : Subgroup X} (hAn : A.Normal)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hK : IsPGroup p ↥(centralizer (A : Set X)))
    (hKab : ∀ c ∈ centralizer (A : Set X), ∀ d ∈ centralizer (A : Set X), c * d = d * c)
    (hmem : ∀ z ∈ centralizer (A : Set X), z ^ p = 1 → z ∈ A)
    (hirr : ∀ B : Subgroup X, B ≤ A → Nat.card B = p → ¬ B.Normal) :
    IsHomocyclicRank2 p ↥(centralizer (A : Set X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let K : Subgroup X := centralizer (A : Set X)
  have hKn : K.Normal := by
    change (centralizer (A : Set X)).Normal
    infer_instance
  have hAK : A ≤ K := by
    intro a ha
    haveI : IsMulCommutative ↥A := hA.1
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A))
  have hAgt : 1 < Nat.card ↥A := by
    rw [hAc]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have hKgt : 1 < Nat.card ↥K := lt_of_lt_of_le hAgt (Subgroup.card_le_of_le hAK)
  have hKne : K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hKgt
    omega
  have hexp : ∃ n : ℕ, ∀ x : ↥K, x ^ (p ^ n) = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    exact ⟨n, fun x => by rw [← hn]; exact pow_card_eq_one'⟩
  let a : ℕ := Nat.find hexp
  have hspec : ∀ x : ↥K, x ^ (p ^ a) = 1 := Nat.find_spec hexp
  have ha0 : a ≠ 0 := by
    intro hzero
    have hsub : Subsingleton ↥K := by
      refine ⟨fun x y => ?_⟩
      have hx : x ^ (p ^ a) = 1 := hspec x
      rw [hzero] at hx
      have hx1 : x = 1 := by simpa using hx
      have hy : y ^ (p ^ a) = 1 := hspec y
      rw [hzero] at hy
      have hy1 : y = 1 := by simpa using hy
      rw [hx1, hy1]
    exact hKne (Subgroup.eq_bot_of_subsingleton K)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
  haveI hKcomm : IsMulCommutative ↥K :=
    IsMulCommutative.of_comm (fun x y => Subtype.ext (hKab x x.2 y y.2))
  let φ : ↥K →* ↥K :=
    { toFun := fun x => x ^ (p ^ (a - 1))
      map_one' := by simp
      map_mul' := fun x y =>
        (Commute.mul_pow ((commute_iff_eq x y).mpr (mul_comm' x y)) (p ^ (a - 1))) }
  let I : Subgroup X := φ.range.map K.subtype
  have hmin : ¬ (∀ x : ↥K, x ^ (p ^ (a - 1)) = 1) :=
    Nat.find_min hexp (m := a - 1) (by omega)
  push Not at hmin
  obtain ⟨x₀, hx₀⟩ := hmin
  have hIA : I ≤ A := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, hx⟩
    have hyK : y ∈ K := by rw [← hzy]; exact z.2
    refine hmem y hyK ?_
    have hzx : (z : ↥K) = x ^ (p ^ (a - 1)) := by rw [← hx]; rfl
    have hconj : (y : X) ^ p = 1 := by
      rw [← hzy, hzx]
      change ((x : X) ^ (p ^ (a - 1))) ^ p = 1
      rw [← pow_mul]
      rw [show (p ^ (a - 1)) * p = p ^ a by rw [← pow_succ, Nat.sub_add_cancel ha]]
      exact congrArg Subtype.val (hspec x)
    simpa using hconj
  have hInorm : I.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
    let xc : ↥K := ⟨g * (x : X) * g⁻¹, hKn.conj_mem (x : X) x.2 g⟩
    have hconj : g * ((φ x : ↥K) : X) * g⁻¹ = ((φ xc : ↥K) : X) := by
      have h1 : ((φ x : ↥K) : X) = (x : X) ^ (p ^ (a - 1)) := rfl
      have h2 : ((φ xc : ↥K) : X) = (g * (x : X) * g⁻¹) ^ (p ^ (a - 1)) := by
        rfl
      rw [h1, h2]
      exact (conj_pow (a := g) (b := (x : X)) (i := p ^ (a - 1))).symm
    change g * ((φ x : ↥K) : X) * g⁻¹ ∈ I
    rw [hconj]
    exact Subgroup.mem_map_of_mem K.subtype (MonoidHom.mem_range.mpr ⟨xc, rfl⟩)
  have hIne : I ≠ ⊥ := by
    intro hIbot
    have hphi : φ x₀ ≠ 1 := by simpa [φ] using hx₀
    have hmem : ((φ x₀ : ↥K) : X) ∈ I :=
      Subgroup.mem_map_of_mem K.subtype (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩)
    rw [hIbot, Subgroup.mem_bot] at hmem
    exact hphi (Subtype.ext hmem)
  have hIcard_dvd : Nat.card I ∣ p ^ 2 := by
    rw [← hAc]
    exact Subgroup.card_dvd_of_le hIA
  have hIcard_eq : Nat.card I = p ^ 2 := by
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hIcard_dvd
    interval_cases k
    · exfalso
      exact hIne (Subgroup.eq_bot_of_card_eq (H := I) (by simpa using hk_eq))
    · exfalso
      exact hirr I hIA (by simpa using hk_eq) hInorm
    · simpa using hk_eq
  have hIAeq : I = A :=
    Subgroup.eq_of_le_of_card_ge hIA (by rw [hIcard_eq, hAc])
  let Ω : Subgroup ↥K := A.subgroupOf K
  have hΩ : ∀ x : ↥K, x ∈ Ω ↔ x ^ p = 1 := by
    intro x
    constructor
    · intro hx
      have hxA : (x : X) ∈ A := Subgroup.mem_subgroupOf.mp hx
      exact Subtype.ext (by simpa using hA.2 (x : X) hxA)
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      have hxp : (x : X) ^ p = 1 := by
        have := congrArg (fun y : ↥K => (y : X)) hx
        simpa using this
      exact hmem (x : X) x.2 hxp
  have hΩcard : Nat.card Ω = p ^ 2 := by
    have e : Ω ≃* A := Subgroup.subgroupOfEquivOfLe hAK
    rw [Nat.card_congr e.toEquiv, hAc]
  have himg : ∀ u ∈ Ω, ∃ x : ↥K, x ^ (p ^ (a - 1)) = u := by
    intro u hu
    have huA : (u : X) ∈ A := Subgroup.mem_subgroupOf.mp hu
    have huI : (u : X) ∈ I := by rw [hIAeq]; exact huA
    rcases Subgroup.mem_map.mp huI with ⟨z, hz, hzu⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hzx : (z : ↥K) = x ^ (p ^ (a - 1)) := by rw [← hx]; rfl
    exact hzx.symm.trans (K.subtype_injective hzu)
  have hhom : Nonempty
      (↥K ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a))) :=
    CFSG.LocalAnalysis.SteinbergBV.homocyclic_of_power_image
      (fun x y : ↥K => Subtype.ext (hKab (x : X) x.2 (y : X) y.2))
      ha hspec Ω hΩ hΩcard himg
  exact ⟨a, ha, hhom⟩


theorem isSLType_quotient_of_map_eq_statedSL [Fact p.Prime] {V : Subgroup X}
    (ρ : X →* GL (Fin 2) (ZMod p)) (hρV : V.map ρ = CFSG.Open.StatedSL 2 (ZMod p)) :
    IsSLType 2 (ZMod p) (↥V ⧸ ρ.ker.subgroupOf V) := by
  let ψ : ↥V →* GL (Fin 2) (ZMod p) := ρ.comp V.subtype
  have hker : ψ.ker = ρ.ker.subgroupOf V := by
    rw [← MonoidHom.comap_ker ρ V.subtype]
    rfl
  have hrange : ψ.range = CFSG.Open.StatedSL 2 (ZMod p) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hρV]
  haveI : (ρ.ker.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  refine ⟨?_⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans
      ((MulEquiv.subgroupCongr hrange).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod p)).symm))


theorem isExtNotation_SL_homocyclic_of_mulEquiv {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂]
    (e : Y₁ ≃* Y₂)
    (h : IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B) Y₁) :
    IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B) Y₂ := by
  obtain ⟨N, hN, hB, hA, hns⟩ := h
  haveI : N.Normal := hN
  let N' : Subgroup Y₂ := N.map (e : Y₁ →* Y₂)
  have hN' : N'.Normal := hN.map (e : Y₁ →* Y₂) e.surjective
  haveI : N'.Normal := hN'
  have hB' : IsHomocyclicRank2 p ↥N' := by
    obtain ⟨n, hn, ⟨f⟩⟩ := hB
    exact ⟨n, hn, ⟨(Subgroup.equivMapOfInjective N (e : Y₁ →* Y₂) e.injective).symm.trans f⟩⟩
  have hA' : IsSLType 2 (ZMod p) (Y₂ ⧸ N') := by
    obtain ⟨f⟩ := hA
    exact ⟨(QuotientGroup.congr N N' e rfl).symm.trans f⟩
  refine ⟨N', hN', hB', hA', ?_⟩
  rintro ⟨H, hH, hinf, hsup⟩
  apply hns
  have hNcomap : N'.comap (e : Y₁ →* Y₂) = N := by
    change (N.map (e : Y₁ →* Y₂)).comap (e : Y₁ →* Y₂) = N
    exact Subgroup.comap_map_eq_self_of_injective e.injective N
  refine ⟨H.comap (e : Y₁ →* Y₂), hH.comap (e : Y₁ →* Y₂), ?_, ?_⟩
  · calc N ⊓ H.comap (e : Y₁ →* Y₂)
        = N'.comap (e : Y₁ →* Y₂) ⊓ H.comap (e : Y₁ →* Y₂) := by rw [hNcomap]
      _ = (N' ⊓ H).comap (e : Y₁ →* Y₂) :=
            (Subgroup.comap_inf N' H (e : Y₁ →* Y₂)).symm
      _ = ⊥ := by
            rw [hinf, MonoidHom.comap_bot, MonoidHom.ker_eq_bot _ e.injective]
  · calc N ⊔ H.comap (e : Y₁ →* Y₂)
        = N'.comap (e : Y₁ →* Y₂) ⊔ H.comap (e : Y₁ →* Y₂) := by rw [hNcomap]
      _ = (N' ⊔ H).comap (e : Y₁ →* Y₂) :=
            (Subgroup.comap_sup_eq (e : Y₁ →* Y₂) N' H e.surjective)
      _ = ⊤ := by rw [hsup, Subgroup.comap_top]


theorem rankTwo_structure (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {A : Subgroup X} (hAn : A.Normal)
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hV : ¬ IsPGroup p ↥(closure {x : X | orderOf x = p})) :
    oPPrimeHull p (⊤ : Subgroup X) = closure {x : X | orderOf x = p} ∧
      IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B)
        ↥(closure {x : X | orderOf x = p}) ∧
      ⁅closure {x : X | orderOf x = p}, closure {x : X | orderOf x = p}⁆ =
        closure {x : X | orderOf x = p} := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : A.Normal := hAn
  have hp2 : p ≠ 2 := by omega
  let S : Set X := {x : X | orderOf x = p}
  let V : Subgroup X := closure S
  let K : Subgroup X := centralizer (A : Set X)
  have hVn : V.Normal := closure_orderOf_normal (X := X) p
  haveI : V.Normal := hVn
  have hKn : K.Normal := by
    change (centralizer (A : Set X)).Normal
    infer_instance
  have hK : IsPGroup p ↥K :=
    isPGroup_centralizer_of_pRank_le_two hp hp2 hX hrk hAn hA hAc
  have hmem : ∀ z ∈ K, z ^ p = 1 → z ∈ A := fun z hz hzp =>
    mem_of_mem_centralizer_of_pow_eq_one hp hrk hA hAc hz hzp
  have hAK : A ≤ K := by
    intro a ha
    haveI : IsMulCommutative ↥A := hA.1
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : ↥A) (⟨a, ha⟩ : ↥A))
  obtain ⟨ρ, hker, hneg⟩ := exists_hom_GL_two hAn hA hAc
  have hkerp : IsPGroup p ↥ρ.ker := hker ▸ hK
  have hρV : V.map ρ = CFSG.Open.StatedSL 2 (ZMod p) :=
    map_closure_orderOf_eq_statedSL ρ hkerp hV
  obtain ⟨t, htV, ht2, htρ⟩ :=
    exists_involution_of_map_eq_statedSL hp2 ρ hkerp hρV
  have hinv : ∀ c ∈ K, t * c * t⁻¹ = c⁻¹ := fun c hc =>
    conj_eq_inv_of_mem_centralizer hp hp2 hAn hK hmem ht2 (hneg t htρ) hc
  have hKcomm : ∀ c ∈ K, ∀ d ∈ K, c * d = d * c :=
    fun c hc d hd => commute_of_conj_eq_inv hinv hc hd
  have hodd : Odd (Nat.card ↥K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    rw [hn]
    exact Odd.pow (n := n) (Nat.Prime.odd_of_ne_two hp hp2)
  have hKc : K ≤ ⁅V, V⁆ := le_commutator_of_conj_eq_inv hVn htV hinv hodd
  have hKV : K ≤ V := hKc.trans (Subgroup.commutator_le_left V V)
  have hirr : ∀ B : Subgroup X, B ≤ A → Nat.card B = p → ¬ B.Normal := by
    intro B hBA hB hBn
    haveI : B.Normal := hBn
    exact (not_le_normalizer_of_card_eq_prime hp hAn hA hAc hK hV hBA hB)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hhom : IsHomocyclicRank2 p ↥K :=
    isHomocyclicRank2_centralizer hp hAn hA hAc hK hKcomm hmem hirr
  have hkerV : ρ.ker ≤ V := hker ▸ hKV
  have hVeq : oPPrimeHull p (⊤ : Subgroup X) = V := by
    apply le_antisymm
    · rw [oPPrimeHull, Subgroup.closure_le]
      rintro x ⟨-, k, hk⟩
      refine mem_closure_orderOf_of_pow_eq_one (ρ := ρ) (hkerV := hkerV) (hρV := hρV)
        (x := x) (k := k) ?_
      rw [← hk]
      exact pow_orderOf_eq_one x
    · rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure ⟨trivial, 1, by rw [pow_one]; exact hx⟩
  have hNnorm : (ρ.ker.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  have hPB : IsHomocyclicRank2 p ↥(ρ.ker.subgroupOf V) := by
    obtain ⟨n, hn, ⟨f⟩⟩ := hhom
    have hNK : ↥(ρ.ker.subgroupOf V) ≃* ↥K :=
      (Subgroup.subgroupOfEquivOfLe (h := hker ▸ hKV)).trans (MulEquiv.subgroupCongr hker)
    exact ⟨n, hn, ⟨hNK.trans f⟩⟩
  have hPA : IsSLType 2 (ZMod p) (↥V ⧸ ρ.ker.subgroupOf V) :=
    isSLType_quotient_of_map_eq_statedSL ρ hρV
  have hns : ¬ ∃ H : Subgroup ↥V, H.Normal ∧
      (ρ.ker.subgroupOf V) ⊓ H = ⊥ ∧ (ρ.ker.subgroupOf V) ⊔ H = ⊤ := by
    rintro ⟨H, hH, hinf, hsup⟩
    haveI : H.Normal := hH
    have hHbot : H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro h hhH
      have hcentA : ∀ a ∈ A, (h : X) * a = a * (h : X) := by
        intro a ha
        have haK : a ∈ K := hAK ha
        have haV : a ∈ V := hKV haK
        let aV : ↥V := ⟨a, haV⟩
        have haN : aV ∈ ρ.ker.subgroupOf V := by
          rw [Subgroup.mem_subgroupOf]
          exact hker ▸ haK
        have hcom : h * aV = aV * h := by
          have hcommH : h * aV * h⁻¹ * aV⁻¹ ∈ H := by
            have h1 : aV * h⁻¹ * aV⁻¹ ∈ H := hH.conj_mem h⁻¹ (H.inv_mem hhH) aV
            have h2 : h * (aV * h⁻¹ * aV⁻¹) ∈ H := H.mul_mem hhH h1
            simpa only [show h * aV * h⁻¹ * aV⁻¹ = h * (aV * h⁻¹ * aV⁻¹) by group]
              using h2
          have hcommN : h * aV * h⁻¹ * aV⁻¹ ∈ ρ.ker.subgroupOf V := by
            have h1 : h * aV * h⁻¹ ∈ ρ.ker.subgroupOf V :=
              hNnorm.conj_mem aV haN h
            have h2 : aV⁻¹ ∈ ρ.ker.subgroupOf V :=
              (ρ.ker.subgroupOf V).inv_mem haN
            have h3 := (ρ.ker.subgroupOf V).mul_mem h1 h2
            simpa only [show h * aV * h⁻¹ * aV⁻¹ = (h * aV * h⁻¹) * aV⁻¹ by group]
              using h3
          have hmem_bot : h * aV * h⁻¹ * aV⁻¹ ∈ (⊥ : Subgroup ↥V) := by
            rw [← hinf]
            exact Subgroup.mem_inf.mpr ⟨hcommN, hcommH⟩
          have hone : h * aV * h⁻¹ * aV⁻¹ = 1 := by simpa using hmem_bot
          calc h * aV = (h * aV * h⁻¹ * aV⁻¹) * (aV * h) := by group
            _ = 1 * (aV * h) := by rw [hone]
            _ = aV * h := one_mul _
        exact congrArg (fun z : ↥V => (z : X)) hcom
      have hhK : (h : X) ∈ K :=
        Subgroup.mem_centralizer_iff.mpr (fun a ha => (hcentA a ha).symm)
      have hhN : h ∈ ρ.ker.subgroupOf V := by
        rw [Subgroup.mem_subgroupOf]
        exact hker ▸ hhK
      have hbot : h ∈ (⊥ : Subgroup ↥V) := by
        rw [← hinf]
        exact Subgroup.mem_inf.mpr ⟨hhN, hhH⟩
      simpa using hbot
    have hNtop : ρ.ker.subgroupOf V = ⊤ := by
      rw [← hsup, hHbot, sup_bot_eq]
    have hVle : V ≤ ρ.ker := by
      intro v hv
      have hmem : (⟨v, hv⟩ : ↥V) ∈ ρ.ker.subgroupOf V := by
        rw [hNtop]
        exact Subgroup.mem_top _
      rwa [Subgroup.mem_subgroupOf] at hmem
    have hVleK : V ≤ K := by
      intro v hv
      have hv' := hVle hv
      rwa [hker] at hv'
    exact hV (hK.to_le hVleK)
  have hcommV : ⁅V, V⁆ = V := by
    apply le_antisymm
    · exact Subgroup.commutator_le_left V V
    · intro v hv
      have hmapcomm : (⁅V, V⁆).map ρ = CFSG.Open.StatedSL 2 (ZMod p) := by
        rw [Subgroup.map_commutator, hρV, commutator_statedSL_eq hp5]
      have hmem : ρ v ∈ (⁅V, V⁆).map ρ := by
        rw [hmapcomm, ← hρV]
        exact Subgroup.mem_map_of_mem ρ hv
      rcases Subgroup.mem_map.mp hmem with ⟨c, hc, hcv⟩
      have hcrel : c⁻¹ * v ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcv, inv_mul_cancel]
      have hmemK : c⁻¹ * v ∈ K := by
        rwa [hker] at hcrel
      have hmemV : c⁻¹ * v ∈ ⁅V, V⁆ := hKc hmemK
      have hv_eq : v = c * (c⁻¹ * v) := by group
      rw [hv_eq]
      exact Subgroup.mul_mem _ hc hmemV
  exact ⟨hVeq, ⟨ρ.ker.subgroupOf V, hNnorm, hPB, hPA, hns⟩, hcommV⟩


theorem rankTwo_structure_of_sixSixOne (h661 : SixSixOneRank) (hp : p.Prime) (hp3 : 3 < p)
    (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hV : ¬ IsPGroup p ↥(closure {x : X | orderOf x = p})) :
    oPPrimeHull p (⊤ : Subgroup X) = closure {x : X | orderOf x = p} ∧
      IsExtNotation (fun B _ => IsSLType 2 (ZMod p) B) (fun B _ => IsHomocyclicRank2 p B)
        ↥(closure {x : X | orderOf x = p}) ∧
      ⁅closure {x : X | orderOf x = p}, closure {x : X | orderOf x = p}⁆ =
        closure {x : X | orderOf x = p} := by
  obtain ⟨A, hAn, hA, hAc⟩ :=
    exists_normal_elemAbelian_of_sixSixOne h661 hp hp3 hX hrk hV
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      intro h
      rw [h] at hp
      norm_num at hp
    omega
  exact rankTwo_structure hp hp5 hX hrk hAn hA hAc hV


end CFSG.LocalAnalysis.RankThreeUC.AGL81C
