module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTwoElt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Tools

variable {X : Type} [Group X] [Finite X]

theorem card_quot_pPrimeCore_le_of_covers {K L F : Subgroup X} (hFK : F ≤ K) (hFL : F ≤ L)
    (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) :
    Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let fK : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  let fL : ↥F →* ↥L ⧸ pPrimeCore 2 ↥L :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hFL)
  have hKs : Function.Surjective fK := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hker : fL.ker ≤ fK.ker := by
    have hN : (fL.ker.map fK).Normal := Subgroup.Normal.map inferInstance fK hKs
    have hcard : Nat.card (fL.ker.map fK) ∣ Nat.card fL.ker := Subgroup.card_map_dvd _ _
    have hodd : Nat.Coprime 2 (Nat.card fL.ker) := by
      let g : fL.ker →* pPrimeCore 2 ↥L :=
        { toFun := fun a => ⟨Subgroup.inclusion hFL (a : ↥F), by
            have h := a.2
            rw [MonoidHom.mem_ker] at h
            exact (QuotientGroup.eq_one_iff _).1 h⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      have hg : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun y : pPrimeCore 2 ↥L => ((y : ↥L) : X)) hab
        exact this
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
        pPrimeCore_coprime_card
    have hle : fL.ker.map fK ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
      le_sSup ⟨hN, (hodd.coprime_dvd_right hcard)⟩
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
    intro a ha
    have : fK a ∈ fL.ker.map fK := ⟨a, ha, rfl⟩
    have := hle this
    rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at this
  let g : ↥F ⧸ fL.ker →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.lift fL.ker fK hker
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := hKs y
    exact ⟨QuotientGroup.mk a, rfl⟩
  calc Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ≤ Nat.card (↥F ⧸ fL.ker) :=
        Nat.card_le_card_of_surjective g hgs
    _ = Nat.card fL.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange fL).toEquiv
    _ ≤ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := Subgroup.card_le_card_group _


omit [Finite X] in
theorem exists_zpow_twoElt_of_pow_mem {O : Subgroup X} {a : X} {j : ℕ}
    (hμ : Nat.Coprime 2 (Nat.card O)) (hab : a ^ (2 ^ j) ∈ O) :
    ∃ n : ℤ, (a ^ n) ^ (2 ^ j) = 1 ∧ a⁻¹ * a ^ n ∈ O := by
  have hbμ : (a ^ (2 ^ j)) ^ Nat.card O = 1 := by
    have h1 : (⟨a ^ (2 ^ j), hab⟩ : ↥O) ^ Nat.card O = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  obtain ⟨u, v, huv⟩ : IsCoprime ((2 ^ j : ℕ) : ℤ) (Nat.card O : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left j hμ)
  refine ⟨v * (Nat.card O : ℤ), ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have e : (v * (Nat.card O : ℤ)) * ((2 ^ j : ℕ) : ℤ) = ((2 ^ j * Nat.card O : ℕ) : ℤ) * v := by
      push_cast
      ring
    rw [e, zpow_mul, zpow_natCast, pow_mul, hbμ, one_zpow]
  · have e : v * (Nat.card O : ℤ) = 1 + ((2 ^ j : ℕ) : ℤ) * (-u) := by linarith
    rw [e, zpow_add, zpow_one, inv_mul_cancel_left, zpow_mul, zpow_natCast]
    exact zpow_mem hab (-u)

theorem exists_twoElt_centralizer_of_comm_mem {K : Subgroup X} {t y : X} (ht : t ^ 2 = 1)
    (hO : t ∈ normalizer (pPrimeCoreOf 2 K : Set X)) (hyK : y ∈ K)
    (hyt : ⁅y, t⁆ ∈ pPrimeCoreOf 2 K) {j : ℕ} (hyj : y ^ (2 ^ j) = 1) :
    ∃ c ∈ K ⊓ centralizer ({t} : Set X), c ^ (2 ^ j) = 1 ∧ c⁻¹ * y ∈ pPrimeCoreOf 2 K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCoreOf 2 K with hOdef
  set N := normalizer (O : Set X)
  have hOK : O ≤ K := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hON : O ≤ N := le_normalizer
  have hKN : K ≤ N := by
    have h : (O.subgroupOf K).Normal := by
      rw [hOdef, pPrimeCoreOf, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
      infer_instance
    exact (normal_subgroupOf_iff_le_normalizer hOK).1 h
  have hMn : (O.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hON).2 le_rfl
  let tN : ↥N := ⟨t, hO⟩
  let yN : ↥N := ⟨y, hKN hyK⟩
  have htN : tN ^ 2 = 1 := Subtype.ext ht
  have hT2 : Fact (IsPGroup 2 ↥(zpowers tN)) := by
    have h1 : orderOf tN ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one htN
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])⟩
  have hμ : Nat.Coprime 2 (Nat.card O) := by
    rw [hOdef, pPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf N)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv]
  set M := O.subgroupOf N with hMdef
  have hcent : centralizer (((zpowers tN).map (QuotientGroup.mk' M) : Subgroup (↥N ⧸ M)) :
      Set (↥N ⧸ M)) = (centralizer ((zpowers tN : Subgroup ↥N) : Set ↥N)).map
        (QuotientGroup.mk' M) :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers tN) M hMn hcop
  have hcommM : ⁅yN, tN⁆ ∈ M := by
    rw [hMdef, Subgroup.mem_subgroupOf]
    exact hyt
  have hq1 : ⁅QuotientGroup.mk' M yN, QuotientGroup.mk' M tN⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).2 hcommM
  have hcq : Commute (QuotientGroup.mk' M tN) (QuotientGroup.mk' M yN) :=
    (commutatorElement_eq_one_iff_mul_comm.1 hq1).symm
  have hmem : QuotientGroup.mk' M yN ∈
      centralizer (((zpowers tN).map (QuotientGroup.mk' M) : Subgroup (↥N ⧸ M)) :
        Set (↥N ⧸ M)) := by
    rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact hcq.zpow_left k
  rw [hcent] at hmem
  obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.1 hmem
  have hay : ((a : ↥N) : X)⁻¹ * y ∈ O := by
    have h1 : a⁻¹ * yN ∈ M := QuotientGroup.eq.1 haq
    rw [hMdef, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hat : ((a : ↥N) : X) * t = t * ((a : ↥N) : X) := by
    have h1 : tN * a = a * tN := (Subgroup.mem_centralizer_iff.1 ha) tN (Subgroup.mem_zpowers tN)
    exact (congrArg Subtype.val h1).symm
  have haK : ((a : ↥N) : X) ∈ K := by
    have h1 : y * (((a : ↥N) : X)⁻¹ * y)⁻¹ ∈ K := K.mul_mem hyK (K.inv_mem (hOK hay))
    have h2 : y * (((a : ↥N) : X)⁻¹ * y)⁻¹ = ((a : ↥N) : X) := by group
    rwa [h2] at h1
  have hab : ((a : ↥N) : X) ^ (2 ^ j) ∈ O := by
    have hy1 : yN ^ (2 ^ j) = 1 := Subtype.ext hyj
    have e : QuotientGroup.mk' M (a ^ (2 ^ j)) = 1 := by
      rw [map_pow, haq, ← map_pow, hy1, map_one]
    have h1 : a ^ (2 ^ j) ∈ M := (QuotientGroup.eq_one_iff _).1 e
    rw [hMdef, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨n, hn1, hn2⟩ := exists_zpow_twoElt_of_pow_mem hμ hab
  refine ⟨((a : ↥N) : X) ^ n, ⟨zpow_mem haK n, ?_⟩, hn1, ?_⟩
  · exact zpow_mem (Subgroup.mem_centralizer_singleton_iff.2 hat) n
  · have e : (((a : ↥N) : X) ^ n)⁻¹ * y
        = (((a : ↥N) : X)⁻¹ * ((a : ↥N) : X) ^ n)⁻¹ * (((a : ↥N) : X)⁻¹ * y) := by group
    rw [e]
    exact O.mul_mem (O.inv_mem hn2) hay

theorem oTwoPrimeOf_inf_centralizer_covers {K : Subgroup X} {t : X} (ht : t ^ 2 = 1)
    (hK : primeResidual 2 ↥K = ⊤) (htc : t ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    (oTwoPrimeOf (K ⊓ centralizer ({t} : Set X))).subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, htO, hcomm⟩ := htc
  rw [eq_top_iff, ← hK, primeResidual_eq_closure, Subgroup.closure_le]
  rintro x ⟨j, hj⟩
  have hxj : (x : X) ^ (2 ^ j) = 1 := by
    have := pow_orderOf_eq_one x
    rw [hj] at this
    exact congrArg Subtype.val this
  obtain ⟨c, hc, hcj, hcy⟩ := exists_twoElt_centralizer_of_comm_mem ht htO x.2
    (hcomm _ x.2) hxj
  have hcK : c ∈ K := hc.1
  have hcF : c ∈ oTwoPrimeOf (K ⊓ centralizer ({t} : Set X)) := mem_oTwoPrimeOf hc j hcj
  have h1 : (⟨c, hcK⟩ : ↥K) ∈ (oTwoPrimeOf (K ⊓ centralizer ({t} : Set X))).subgroupOf K := hcF
  have h2 : (⟨c, hcK⟩ : ↥K)⁻¹ * x ∈ pPrimeCore 2 ↥K := by
    obtain ⟨w, hw, hwe⟩ := hcy
    have : w = (⟨c, hcK⟩ : ↥K)⁻¹ * x := Subtype.ext hwe
    rwa [← this]
  have : x = ⟨c, hcK⟩ * ((⟨c, hcK⟩ : ↥K)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup h1 h2

theorem covers_of_card_le {E M : Subgroup X} (hEM : E ≤ M)
    (hcard : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ≤ Nat.card (↥E ⧸ pPrimeCore 2 ↥E)) :
    E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥E →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hEM)
  have hker : φ.ker ≤ pPrimeCore 2 ↥E := by
    have hodd : Nat.Coprime 2 (Nat.card φ.ker) := by
      let g : φ.ker →* pPrimeCore 2 ↥M :=
        { toFun := fun a => ⟨Subgroup.inclusion hEM (a : ↥E), by
            have h := a.2
            rw [MonoidHom.mem_ker] at h
            exact (QuotientGroup.eq_one_iff _).1 h⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      have hg : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun y : pPrimeCore 2 ↥M => ((y : ↥M) : X)) hab
        exact this
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
        pPrimeCore_coprime_card
    exact le_sSup ⟨inferInstance, hodd⟩
  let q : ↥E ⧸ φ.ker →* ↥E ⧸ pPrimeCore 2 ↥E := QuotientGroup.map φ.ker (pPrimeCore 2 ↥E)
    (MonoidHom.id _) hker
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have h1 : Nat.card (↥E ⧸ pPrimeCore 2 ↥E) ≤ Nat.card φ.range :=
    (Nat.card_le_card_of_surjective q hqs).trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).le
  have h2 : Nat.card φ.range ≤ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := Subgroup.card_le_card_group _
  have hrange : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    omega
  rw [eq_top_iff]
  intro x _
  have hx : (QuotientGroup.mk x : ↥M ⧸ pPrimeCore 2 ↥M) ∈ φ.range :=
    hrange ▸ Subgroup.mem_top _
  obtain ⟨e, he⟩ := hx
  have h3 : (Subgroup.inclusion hEM e)⁻¹ * x ∈ pPrimeCore 2 ↥M := by
    have : (QuotientGroup.mk (Subgroup.inclusion hEM e) : ↥M ⧸ pPrimeCore 2 ↥M) =
        QuotientGroup.mk x := he
    rw [QuotientGroup.eq] at this
    exact this
  have h4 : Subgroup.inclusion hEM e ∈ E.subgroupOf M := e.2
  have h5 : x = Subgroup.inclusion hEM e * ((Subgroup.inclusion hEM e)⁻¹ * x) := by group
  rw [h5]
  exact Subgroup.mul_mem_sup h4 h3

end Tools

section Helpers
theorem pPrimeCore_le_normalizer_of_isPComponent {D : Type*} [Group D] [Finite D]
    {M : Subgroup D} (hM : IsPComponent 2 M) : pPrimeCore 2 D ≤ normalizer (M : Set D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pPrimeCore 2 D).IsSubnormal :=
    (inferInstance : (pPrimeCore 2 D).Normal).isSubnormal
  rcases contains_or_normalizes_core 2 M (pPrimeCore 2 D) hM hN with hle | ⟨hnorm, -⟩
  · exfalso
    obtain ⟨K, hK, -, hMK, -⟩ := hM
    have hbot : M.map (QuotientGroup.mk' (pPrimeCore 2 D)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hle
    rw [hMK] at hbot
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hbot
  · exact hnorm
theorem primeResidual_oTwoPrimeOf {X : Type} [Group X] [Finite X] (A : Subgroup X) :
    primeResidual 2 ↥(oTwoPrimeOf A) = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [primeResidual_eq_closure, eq_top_iff]
  intro y _
  have hmap : oTwoPrimeOf A ≤
      (Subgroup.closure {z : ↥(oTwoPrimeOf A) | ∃ k : ℕ, orderOf z = 2 ^ k}).map
        (oTwoPrimeOf A).subtype := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxA, k, hk⟩
    apply Subgroup.subset_closure
    have hxB : x ∈ oTwoPrimeOf A := mem_oTwoPrimeOf hxA k hk
    refine ⟨⟨x, hxB⟩, ?_, rfl⟩
    have hdvd : orderOf (⟨x, hxB⟩ : ↥(oTwoPrimeOf A)) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using hk)
    obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k', hk'⟩
  obtain ⟨z, hz, hzy⟩ := hmap y.2
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz
theorem nonempty_quot_mulEquiv_of_covers {X : Type} [Group X] [Finite X] {F K : Subgroup X}
    (hFK : F ≤ K) (hcov : F.subgroupOf K ⊔ pPrimeCore 2 ↥K = ⊤) :
    Nonempty ((↥F ⧸ pPrimeCore 2 ↥F) ≃* (↥K ⧸ pPrimeCore 2 ↥K)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥F →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hFK)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hx : x ∈ F.subgroupOf K ⊔ pPrimeCore 2 ↥K := hcov ▸ Subgroup.mem_top x
    obtain ⟨f, hf, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨(f : X), hf⟩, ?_⟩
    have h1 : (QuotientGroup.mk (f * o) : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk f := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rw [h1]
    rfl
  have hker1 : φ.ker ≤ pPrimeCore 2 ↥F := by
    have hodd : Nat.Coprime 2 (Nat.card φ.ker) := by
      let g : φ.ker →* pPrimeCore 2 ↥K :=
        { toFun := fun a => ⟨Subgroup.inclusion hFK (a : ↥F), by
            have h := a.2
            rw [MonoidHom.mem_ker] at h
            exact (QuotientGroup.eq_one_iff _).1 h⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      have hg : Function.Injective g := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun y : pPrimeCore 2 ↥K => ((y : ↥K) : X)) hab
        exact this
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
        pPrimeCore_coprime_card
    exact le_sSup ⟨inferInstance, hodd⟩
  have hker2 : pPrimeCore 2 ↥F ≤ φ.ker := by
    have hN : ((pPrimeCore 2 ↥F).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have hcard : Nat.card ((pPrimeCore 2 ↥F).map φ) ∣ Nat.card (pPrimeCore 2 ↥F) :=
      Subgroup.card_map_dvd _ _
    have hle : (pPrimeCore 2 ↥F).map φ ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
      le_sSup ⟨hN, Nat.Coprime.coprime_dvd_right hcard pPrimeCore_coprime_card⟩
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at hle
    intro a ha
    have h1 : φ a ∈ (pPrimeCore 2 ↥F).map φ := ⟨a, ha, rfl⟩
    have h2 := hle h1
    rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker] at h2
  have hker : φ.ker = pPrimeCore 2 ↥F := le_antisymm hker1 hker2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
theorem normal_subgroupOf_oTwoPrimeOf {X : Type} [Group X] (A : Subgroup X) :
    ((oTwoPrimeOf A).subgroupOf A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hle : oTwoPrimeOf A ≤ (oTwoPrimeOf A).comap (MulAut.conj (g : X)).toMonoidHom := by
    rw [oTwoPrimeOf_le_iff]
    intro x hx h2
    rw [Subgroup.mem_comap]
    exact mem_oTwoPrimeOf_of_twoElt (A.mul_mem (A.mul_mem g.2 hx) (A.inv_mem g.2)) (h2.conj g)
  simpa using hle hn
end Helpers

end CFSG.OddStandard.Solomon75
