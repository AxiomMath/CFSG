module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Model
import CFSG.Quasithin.Background.G64RealizeSec
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourFixedAutomorphism

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (commV fixV twoResidual BinaryNaturalSL FFModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.Open
open scoped Matrix

variable {V : Type} [CommGroup V] [Finite V]

private theorem card_statedSL_two_eq_six_ba3s {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Nat.card ↥(StatedSL 2 K) = 6 := by
  rw [CFSG.Open.StatedAPI.card_statedSL_two, hK]
  norm_num

omit [Finite V] in
private theorem card_N_of_isSLn_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1) :
    Nat.card ↥N = 6 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eN⟩⟩ := hN
  let : Field K := hKf
  let : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  exact (Nat.card_congr eN.toEquiv).trans (card_statedSL_two_eq_six_ba3s hK2)

private theorem twoResidual_ne_bot_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1) :
    twoResidual N ≠ ⊥ := by
  have hcardN : Nat.card ↥N = 6 := card_N_of_isSLn_ba3s hN
  intro hT
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 (by rw [hcardN]; norm_num)
  obtain ⟨k, hk⟩ := CFSG.Quasithin.twoResidual_isTwoQuotient N (x : MulAut V) x.2
  rw [hT, Subgroup.mem_bot] at hk
  have hd : orderOf (x : MulAut V) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  rw [Subgroup.orderOf_coe x, hxord] at hd
  exact absurd ((show Nat.Prime 3 by norm_num).dvd_of_dvd_pow hd) (by norm_num)

private theorem twoResidual_le_sylow3_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1) :
    ∃ P₃ : Subgroup (MulAut V), twoResidual N ≤ P₃ ∧ Nat.card P₃ = 3 := by
  have hcardN : Nat.card ↥N = 6 := card_N_of_isSLn_ba3s hN
  obtain ⟨K₃, hK₃card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 3 (n := 1)
    (by rw [pow_one, hcardN]; norm_num)
  let P₃ : Subgroup (MulAut V) := K₃.map N.subtype
  have hP₃le : P₃ ≤ N := Subgroup.map_subtype_le K₃
  have hP₃card : Nat.card P₃ = 3 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hK₃card]
    norm_num
  have hcardSub : Nat.card ↥(P₃.subgroupOf N) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₃le).toEquiv).trans hP₃card
  have hP₃idx : (P₃.subgroupOf N).index = 2 := by
    have hmul := Subgroup.card_mul_index (H := P₃.subgroupOf N)
    rw [hcardSub, hcardN] at hmul
    omega
  have hP₃norm : (P₃.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two hP₃idx
  have hnormP₃ : N ≤ Subgroup.normalizer (P₃ : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP₃le).mp hP₃norm
  have h2 : ∀ y ∈ N, ∃ k : ℕ, y ^ 2 ^ k ∈ P₃ := by
    intro y hy
    refine ⟨1, ?_⟩
    have : (P₃.subgroupOf N).Normal := hP₃norm
    have : Fintype ↥N := Fintype.ofFinite ↥N
    have : Fintype (↥N ⧸ (P₃.subgroupOf N)) := Fintype.ofFinite _
    let yN : ↥N := ⟨y, hy⟩
    have hqcard : Nat.card (↥N ⧸ (P₃.subgroupOf N)) = 2 := by
      rw [← Subgroup.index_eq_card, hP₃idx]
    have hq : (yN : ↥N ⧸ (P₃.subgroupOf N)) ^ 2 = 1 := by
      have h := pow_card_eq_one (x := (yN : ↥N ⧸ (P₃.subgroupOf N)))
      rw [← Nat.card_eq_fintype_card, hqcard] at h
      exact h
    have hqm : yN ^ 2 ∈ P₃.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff (x := yN ^ 2), QuotientGroup.mk_pow]
      exact hq
    simpa [yN] using (Subgroup.mem_subgroupOf.mp hqm)
  exact ⟨P₃, CFSG.Quasithin.twoResidual_le_of_isTwoQuotient hP₃le hnormP₃ h2, hP₃card⟩

private theorem twoResidual_card_three_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1) :
    Nat.card ↥(twoResidual N) = 3 := by
  obtain ⟨P₃, hTle, hP₃card⟩ := twoResidual_le_sylow3_ba3s hN
  have hTne : twoResidual N ≠ ⊥ := twoResidual_ne_bot_ba3s hN
  have hdivT : Nat.card ↥(twoResidual N) ∣ 3 := by
    rw [← hP₃card]
    calc Nat.card ↥(twoResidual N)
        = Nat.card ↥((twoResidual N).subgroupOf P₃) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv).symm
      _ ∣ Nat.card ↥P₃ := Subgroup.card_subgroup_dvd_card _
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdivT with h1 | h3
  · exfalso
    apply hTne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have : Subsingleton ↥(twoResidual N) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥(twoResidual N)) 1)
  · exact h3

private theorem map_commV_mem_ba3s {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)}
    {g : MulAut V} (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    ∀ c ∈ commV X, g c ∈ commV X := by
  intro c hc
  have hle : commV X ≤ (commV X).comap g.toMonoidHom := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact Subgroup.subset_closure ⟨g * x * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hg x).mp hx, g v, by simp [MulAut.mul_apply]⟩
  exact hle hc

private theorem commV_invariant_iff_ba3s {V : Type*} [CommGroup V] (X : Subgroup (MulAut V))
    {g : MulAut V} (hg : g ∈ Subgroup.normalizer (X : Set (MulAut V))) :
    ∀ v : V, g v ∈ commV X ↔ v ∈ commV X := by
  intro v
  constructor
  · intro hv
    have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set (MulAut V)) :=
      (Subgroup.normalizer (X : Set (MulAut V))).inv_mem hg
    have := map_commV_mem_ba3s (V := V) hg' (g v) hv
    simpa using this
  · exact map_commV_mem_ba3s (V := V) hg v

private noncomputable def restrictMulAut_ba3s {V : Type*} [CommGroup V] (U : Subgroup V)
    (t : MulAut V) (h : ∀ x : V, t x ∈ U ↔ x ∈ U) : MulAut ↥U where
  toFun u := ⟨t u, (h u).mpr u.2⟩
  invFun u := ⟨t⁻¹ u, (h (t⁻¹ u)).mp (by simp)⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (map_mul t (u : V) (v : V))

private noncomputable def rhoHom_ba3s {V : Type*} [CommGroup V] (U : Subgroup V)
    (X : Subgroup (MulAut V)) (hX : ∀ x ∈ X, ∀ v : V, x v ∈ U ↔ v ∈ U) :
    ↥X →* MulAut ↥U where
  toFun x := restrictMulAut_ba3s U x (hX x x.2)
  map_one' := by apply MulEquiv.ext; intro u; rfl
  map_mul' a b := by apply MulEquiv.ext; intro u; rfl

private noncomputable def rhoT_ba3s (N : Subgroup (MulAut V)) :
    ↥(twoResidual N) →* MulAut ↥(commV N) :=
  rhoHom_ba3s (commV N) (twoResidual N)
    (fun _ hy => commV_invariant_iff_ba3s N
      (Subgroup.le_normalizer (CFSG.Quasithin.twoResidual_le N hy)))

private theorem charP_two_of_card_two_ba3s {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  refine charP_of_card_eq_prime_pow (p := 2) (f := 1) ?_
  rw [pow_one, ← Nat.card_eq_fintype_card, hK]

omit [Finite V] in
private theorem commV_model_data_ba3s {N : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {π₀ : ↥(StatedSL 2 K) →* ↥N}
    (hVIA : (FFModel.nat (StatedSL 2 K)).RealizesVia N (commV N) ⊥ π₀) :
    ∃ E : ↥(commV N) ≃* Multiplicative (Fin 2 → K),
      (∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commV N))
        (hu : ((π₀ γ : ↥N) : MulAut V) (u : V) ∈ commV N),
        E ⟨((π₀ γ : ↥N) : MulAut V) (u : V), hu⟩ =
          CFSG.Quasithin.natAct (StatedSL 2 K) γ (E u)) ∧
      Nat.card ↥(commV N) = 4 ∧ (∀ u : ↥(commV N), u ^ 2 = 1) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.G64.RealizesVia.exists_secMap
    (D := FFModel.nat (StatedSL 2 K)) rfl hVIA
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : V) ∈ (⊥ : Subgroup V) := (hfk u).mp hu
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  let E' : ↥(commV N) ≃* ↥(FFModel.nat (StatedSL 2 K)).sec :=
    MulEquiv.ofBijective f ⟨hfi, hfs⟩
  let E : ↥(commV N) ≃* Multiplicative (Fin 2 → K) :=
    E'.trans (Subgroup.topEquiv (G := Multiplicative (Fin 2 → K)))
  refine ⟨E, ?_, ?_, ?_⟩
  · intro γ u hu
    exact hfe γ u hu
  · calc Nat.card ↥(commV N) = Nat.card (Multiplicative (Fin 2 → K)) := Nat.card_congr E.toEquiv
      _ = Nat.card (Fin 2 → K) := (Nat.card_congr (Multiplicative.ofAdd (α := Fin 2 → K))).symm
      _ = 4 := by rw [Nat.card_fun, hK]; norm_num
  · intro u
    have : CharP K 2 := charP_two_of_card_two_ba3s hK
    have hx2 : ∀ x : K, x + x = 0 := by
      intro x
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc x + x = (2 : K) * x := by ring
        _ = 0 := by rw [h2, zero_mul]
    have hsq : ∀ v : Multiplicative (Fin 2 → K), v * v = 1 := by
      intro v
      rw [← ofAdd_toAdd v, ← ofAdd_add]
      have hw : Multiplicative.toAdd v + Multiplicative.toAdd v = 0 := by
        funext i
        exact hx2 _
      rw [hw]
      rfl
    apply E.injective
    rw [map_pow, map_one]
    simpa [pow_two] using hsq (E u)

omit [Finite V] in
private theorem rhoT_ne_one_ba3s {N : Subgroup (MulAut V)}
    (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1) :
    ∀ x : ↥(twoResidual N), x ≠ 1 → rhoT_ba3s N x ≠ 1 := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  let : Field K := hKf
  let : Finite K := hKfin
  have hK : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨π₀, hVIA⟩ := hreal
  obtain ⟨E, hE, -, -⟩ := commV_model_data_ba3s hK hVIA
  intro x hx hρ
  have hcon : ∀ u : ↥(commV N), ((x : MulAut V) (u : V)) = (u : V) := by
    intro u
    have h2 : ((rhoT_ba3s N x) u : V) = (u : V) := by
      have := congrArg (fun f : MulAut ↥(commV N) => f u) hρ
      simpa using congrArg Subtype.val this
    simpa [rhoT_ba3s, rhoHom_ba3s, restrictMulAut_ba3s] using h2
  let xN : ↥N := ⟨(x : MulAut V), CFSG.Quasithin.twoResidual_le N x.2⟩
  obtain ⟨g, hg⟩ := hVIA.1 xN
  have hgW : ((π₀ g : ↥N) : MulAut V) = ((xN : ↥N) : MulAut V) :=
    congrArg (fun y : ↥N => (y : MulAut V)) hg
  have htriv : ∀ v : Multiplicative (Fin 2 → K),
      CFSG.Quasithin.natAct (StatedSL 2 K) g v = v := by
    intro v
    obtain ⟨u, rfl⟩ := E.surjective v
    have hu : ((π₀ g : ↥N) : MulAut V) (u : V) ∈ commV N := by
      rw [hgW]
      exact (commV_invariant_iff_ba3s N
        (Subgroup.le_normalizer (CFSG.Quasithin.twoResidual_le N x.2)) (u : V)).mpr u.2
    rw [← hE g u hu]
    exact congrArg E (Subtype.ext (by
      calc ((π₀ g : ↥N) : MulAut V) (u : V)
          = ((xN : ↥N) : MulAut V) (u : V) := congrArg (fun f : MulAut V => f (u : V)) hgW
        _ = (x : MulAut V) (u : V) := rfl
        _ = (u : V) := hcon u))
  have hg1 : g = 1 := by
    apply CFSG.Quasithin.natAct_faithful (StatedSL 2 K) g
    intro m
    rw [htriv m, mul_inv_cancel]
  have hxN1 : xN = 1 := by rw [← hg, hg1, map_one]
  have hxW : (x : MulAut V) = 1 := by
    have := congrArg (fun y : ↥N => (y : MulAut V)) hxN1
    simpa [xN] using this
  exact hx (Subtype.ext hxW)

private theorem isKleinFour_of_card_four_ba3s {V : Type*} [CommGroup V]
    (h4 : Nat.card V = 4) (h2 : ∀ x : V, x ^ 2 = 1) : IsKleinFour V := by
  refine ⟨h4, ?_⟩
  have hex : Monoid.exponent V ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      simpa [pow_two] using h2 x
  rcases (Nat.dvd_prime Nat.prime_two).mp hex with h | h
  · exfalso
    have : Subsingleton V := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : V)
    omega
  · exact h

private theorem eq_one_of_fixed_of_pow_three_ba3s {V : Type*} [CommGroup V]
    (h4 : Nat.card V = 4) (h2 : ∀ x : V, x ^ 2 = 1) (φ : MulAut V) (hφ3 : φ ^ 3 = 1)
    (hφne : φ ≠ 1) : ∀ u : V, φ u = u → u = 1 := by
  intro u hu
  by_contra hu1
  have : IsKleinFour V := isKleinFour_of_card_four_ba3s h4 h2
  have h2' : φ ^ 2 = 1 :=
    CFSG.GorensteinWalter.mulAut_sq_eq_one_of_fixed_ne_one φ hu1 hu
  apply hφne
  have hdvd : orderOf φ ∣ Nat.gcd 2 3 :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h2') (orderOf_dvd_iff_pow_eq_one.mpr hφ3)
  rw [show Nat.gcd 2 3 = 1 from by norm_num, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.mp hdvd

private theorem fpf_commV_ba3s {N : Subgroup (MulAut V)}
    (hN : IsSLn ↥N 2 1) (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1)
    (hU4 : Nat.card ↥(commV N) = 4) (hU2 : ∀ u : ↥(commV N), u ^ 2 = 1) :
    ∀ x : ↥(twoResidual N), x ≠ 1 → ∀ u ∈ commV N, (x : MulAut V) u = u → u = 1 := by
  intro x hx u hu hux
  have hρ3 : rhoT_ba3s N x ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥(twoResidual N)) (x := x)
      rwa [twoResidual_card_three_ba3s hN] at h
    rw [← map_pow, hx3, map_one]
  have hρne : rhoT_ba3s N x ≠ 1 := rhoT_ne_one_ba3s hnat x hx
  have hfix : rhoT_ba3s N x ⟨u, hu⟩ = ⟨u, hu⟩ := by
    apply Subtype.ext
    simpa [rhoT_ba3s, rhoHom_ba3s, restrictMulAut_ba3s] using hux
  exact congrArg Subtype.val
    (eq_one_of_fixed_of_pow_three_ba3s hU4 hU2 (rhoT_ba3s N x) hρ3 hρne ⟨u, hu⟩ hfix)

private theorem commV_twoResidual_eq_ba3s {N : Subgroup (MulAut V)}
    {t : ↥N} (ht : (t : MulAut V) ∈ twoResidual N)
    (hfpf : ∀ u ∈ commV N, (t : MulAut V) u = u → u = 1) :
    commV (twoResidual N) = commV N := by
  have hle : commV (twoResidual N) ≤ commV N := by
    apply Subgroup.closure_mono
    rintro w ⟨x, hx, v, rfl⟩
    exact ⟨x, CFSG.Quasithin.twoResidual_le N hx, v, rfl⟩
  refine le_antisymm hle ?_
  have hUinv : ∀ v ∈ commV N, (t : MulAut V) v * v⁻¹ ∈ commV N := fun v _ =>
    Subgroup.subset_closure
      ⟨(t : MulAut V), CFSG.Quasithin.twoResidual_le N ht, v, rfl⟩
  let φ : ↥(commV N) → ↥(commV N) := fun v =>
    ⟨(t : MulAut V) (v : V) * (v : V)⁻¹, hUinv (v : V) v.2⟩
  have hφinj : Function.Injective φ := by
    intro v w h
    have h' : (t : MulAut V) (v : V) * (v : V)⁻¹ =
        (t : MulAut V) (w : V) * (w : V)⁻¹ := congrArg Subtype.val h
    have h5 : (t : MulAut V) (v : V) * (v : V)⁻¹ * (w : V) = (t : MulAut V) (w : V) := by
      have := congrArg (fun z => z * (w : V)) h'
      simpa [mul_assoc] using this
    have h2 : (t : MulAut V) ((v : V)⁻¹ * (w : V)) = (v : V)⁻¹ * (w : V) := by
      calc (t : MulAut V) ((v : V)⁻¹ * (w : V))
          = ((t : MulAut V) (v : V))⁻¹ * (t : MulAut V) (w : V) := by rw [map_mul, map_inv]
        _ = ((t : MulAut V) (v : V))⁻¹ *
              ((t : MulAut V) (v : V) * (v : V)⁻¹ * (w : V)) := by rw [← h5]
        _ = (v : V)⁻¹ * (w : V) := by group
    have hmem : (v : V)⁻¹ * (w : V) ∈ commV N :=
      (commV N).mul_mem ((commV N).inv_mem v.2) w.2
    exact Subtype.ext (inv_mul_eq_one.mp (hfpf _ hmem h2))
  have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
  intro u hu
  obtain ⟨v, hv⟩ := hφsurj ⟨u, hu⟩
  have hvu : u = (φ v).val := (congrArg Subtype.val hv).symm
  rw [hvu]
  exact Subgroup.subset_closure
    ⟨(t : MulAut V), ht, (v : V), rfl⟩

private theorem isAlt_three_of_isSLn_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1) :
    IsAlt ↥(twoResidual N) 3 := by
  have hTcard : Nat.card ↥(twoResidual N) = 3 := twoResidual_card_three_ba3s hN
  have : IsCyclic ↥(twoResidual N) := isCyclic_of_prime_card (p := 3) hTcard
  have : IsCyclic ↥(alternatingGroup (Fin 3)) :=
    isCyclic_of_prime_card (p := 3) CFSG.QuasithinUnique.L246.card_alt3
  exact ⟨mulEquivOfCyclicCardEq (by rw [hTcard, CFSG.QuasithinUnique.L246.card_alt3])⟩

private theorem fpf_commV_of_model_ba3s {N : Subgroup (MulAut V)}
    (hN : IsSLn ↥N 2 1) (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1) :
    ∀ x : ↥(twoResidual N), x ≠ 1 → ∀ u ∈ commV N, (x : MulAut V) u = u → u = 1 := by
  have hnat' : BinaryNaturalSL N (commV N) ⊥ 2 1 := hnat
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  let : Field K := hKf
  let : Finite K := hKfin
  have hK : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨π₀, hVIA⟩ := hreal
  obtain ⟨E, hE, hU4, hU2⟩ := commV_model_data_ba3s hK hVIA
  exact fpf_commV_ba3s hN hnat' hU4 hU2

omit [Finite V] in
private theorem commV_data_ba3s {N : Subgroup (MulAut V)}
    (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1) :
    Nat.card ↥(commV N) = 4 ∧ (∀ u : ↥(commV N), u ^ 2 = 1) := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  let : Field K := hKf
  let : Finite K := hKfin
  have hK : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨π₀, hVIA⟩ := hreal
  obtain ⟨E, hE, hU4, hU2⟩ := commV_model_data_ba3s hK hVIA
  exact ⟨hU4, hU2⟩

private theorem hirr_rhoT_ba3s {N : Subgroup (MulAut V)} (hN : IsSLn ↥N 2 1)
    (hfpf : ∀ x : ↥(twoResidual N), x ≠ 1 → ∀ u ∈ commV N, (x : MulAut V) u = u → u = 1)
    (hU4 : Nat.card ↥(commV N) = 4) :
    ∀ J : Subgroup ↥(commV N),
      (∀ γ ∈ (rhoT_ba3s N).range, ∀ y ∈ J, γ y ∈ J) → J = ⊥ ∨ J = ⊤ := by
  have hTcard : Nat.card ↥(twoResidual N) = 3 := twoResidual_card_three_ba3s hN
  have : Nontrivial ↥(twoResidual N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
  obtain ⟨t0, ht0⟩ := exists_ne (1 : ↥(twoResidual N))
  intro J hJ
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  by_cases htop : J = ⊤
  · exact Or.inr htop
  exfalso
  have hdiv : Nat.card ↥J ∣ Nat.card ↥(commV N) := Subgroup.card_subgroup_dvd_card J
  rw [hU4, show (4 : ℕ) = 2 ^ 2 from by norm_num] at hdiv
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  interval_cases k
  · exact hbot (Subgroup.eq_bot_of_card_eq (H := J) (by rw [hk_eq]; norm_num))
  · have hcardJ : Nat.card ↥J = 2 := by rw [hk_eq]; norm_num
    obtain ⟨y, hy1, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥J)).1 hcardJ
    let yU : ↥(commV N) := (y : ↥(commV N))
    have hmem : rhoT_ba3s N t0 yU ∈ J := by
      simpa [yU] using hJ (rhoT_ba3s N t0) ⟨t0, rfl⟩ y y.2
    let z : ↥J := ⟨rhoT_ba3s N t0 yU, hmem⟩
    have hyU1 : yU ≠ 1 := fun h =>
      hy1 (Subtype.ext (by simpa [yU] using congrArg Subtype.val h))
    have hz1 : z ≠ 1 := by
      intro h
      have h1 : rhoT_ba3s N t0 yU = 1 := by
        have := congrArg Subtype.val h
        simpa [z] using this
      exact hyU1 (((rhoT_ba3s N t0).injective) (by rw [h1, map_one]))
    have hyu : rhoT_ba3s N t0 yU = yU := congrArg Subtype.val (hyuniq z hz1)
    have hfix : (t0 : MulAut V) (yU : V) = (yU : V) := congrArg Subtype.val hyu
    have hyV : (y : V) = 1 := by
      simpa [yU] using hfpf t0 ht0 (yU : V) yU.2 hfix
    exact hy1 (Subtype.ext (Subtype.ext hyV))
  · exact htop (Subgroup.eq_top_of_card_eq (H := J) (by rw [hk_eq, hU4]; norm_num))

omit [Finite V] in
private theorem transport_ba3s {N : Subgroup (MulAut V)}
    (hρinj : Function.Injective (rhoT_ba3s N))
    {π : ↥(alternatingGroup (Fin 3)) →* ↥(rhoT_ba3s N).range}
    (hπRV : (FFModel.altDn 3).RealizesVia (rhoT_ba3s N).range ⊤ ⊥ π) :
    ∃ π' : ↥(alternatingGroup (Fin 3)) →* ↥(twoResidual N),
      (FFModel.altDn 3).RealizesVia (twoResidual N) (commV N) ⊥ π' := by
  let e : ↥(twoResidual N) ≃* ↥(rhoT_ba3s N).range :=
    MulEquiv.ofBijective (rhoT_ba3s N).rangeRestrict
      ⟨(rhoT_ba3s N).rangeRestrict_injective_iff.mpr hρinj,
        (rhoT_ba3s N).rangeRestrict_surjective⟩
  let π' : ↥(alternatingGroup (Fin 3)) →* ↥(twoResidual N) := e.symm.toMonoidHom.comp π
  have he : ∀ γ, e (π' γ) = π γ := fun γ => e.apply_symm_apply (π γ)
  have hact : ∀ γ : ↥(alternatingGroup (Fin 3)),
      ((π γ : ↥(rhoT_ba3s N).range) : MulAut ↥(commV N)) = rhoT_ba3s N (π' γ) := by
    intro γ
    rw [← he γ]
    rfl
  refine ⟨π', ?_⟩
  refine ⟨e.symm.surjective.comp hπRV.1, bot_le, hπRV.2.2.1, ?_, ?_,
    hπRV.2.2.2.2.2.1, hπRV.2.2.2.2.2.2.1, ?_⟩
  · intro h u hu
    exact map_commV_mem_ba3s (V := V)
      (Subgroup.le_normalizer (CFSG.Quasithin.twoResidual_le N h.2)) u hu
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · obtain ⟨βΓ, hβΓsurj, hβΓker, hβΓeq⟩ := hπRV.2.2.2.2.2.2.2
    let β : ↥(commV N) →* (↥(FFModel.altDn 3).sec ⧸
        (FFModel.altDn 3).ker.subgroupOf (FFModel.altDn 3).sec) :=
      βΓ.comp (Subgroup.topEquiv (G := ↥(commV N))).symm.toMonoidHom
    refine ⟨β, hβΓsurj.comp (Subgroup.topEquiv (G := ↥(commV N))).symm.surjective, ?_, ?_⟩
    · intro u
      rw [MonoidHom.comp_apply, hβΓker, Subgroup.mem_bot, Subgroup.mem_bot]
      exact ⟨fun h => by simpa using congrArg Subtype.val h,
        fun h => Subtype.ext (by simpa using h)⟩
    · intro γ u m hu hm hβ
      have hβ' : βΓ (Subgroup.topEquiv.symm u) = QuotientGroup.mk m := hβ
      have hkey : (π γ : MulAut ↥(commV N))
            ((Subgroup.topEquiv.symm u : ↥(⊤ : Subgroup ↥(commV N))) : ↥(commV N)) =
          ⟨((π' γ : ↥(twoResidual N)) : MulAut V) (u : V), hu⟩ := by
        rw [hact γ]
        apply Subtype.ext
        rfl
      have harg : (⟨(π γ : MulAut ↥(commV N))
            ((Subgroup.topEquiv.symm u : ↥(⊤ : Subgroup ↥(commV N))) : ↥(commV N)), trivial⟩ :
            ↥(⊤ : Subgroup ↥(commV N))) =
          ⟨⟨((π' γ : ↥(twoResidual N)) : MulAut V) (u : V), hu⟩, trivial⟩ :=
        Subtype.ext hkey
      have h1 := hβΓeq γ (Subgroup.topEquiv.symm u) m trivial hm hβ'
      exact (congrArg βΓ harg) ▸ h1

private theorem realizes_altDn_three_ba3s {N : Subgroup (MulAut V)}
    (hN : IsSLn ↥N 2 1) (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1) :
    (FFModel.altDn 3).Realizes (twoResidual N) (commV (twoResidual N))
      (gomiWXKer (twoResidual N)) := by
  classical
  have hTcard : Nat.card ↥(twoResidual N) = 3 := twoResidual_card_three_ba3s hN
  have hfpf := fpf_commV_of_model_ba3s hN hnat
  obtain ⟨hU4, hU2⟩ := commV_data_ba3s hnat
  have : Nontrivial ↥(twoResidual N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
  obtain ⟨t0, ht0⟩ := exists_ne (1 : ↥(twoResidual N))
  let tN : ↥N := ⟨(t0 : MulAut V), CFSG.Quasithin.twoResidual_le N t0.2⟩
  have hcommV : commV (twoResidual N) = commV N :=
    commV_twoResidual_eq_ba3s (t := tN) t0.2 (hfpf t0 ht0)
  have hker : gomiWXKer (twoResidual N) = ⊥ := by
    rw [gomiWXKer, hcommV, Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨hwU, hwfix⟩ := hw
    exact hfpf t0 ht0 w hwU (hwfix _ t0.2)
  have hρinj : Function.Injective (rhoT_ba3s N) := by
    intro x y hxy
    have hx : rhoT_ba3s N (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h1 : x * y⁻¹ = 1 := by
      by_contra hne
      exact rhoT_ne_one_ba3s hnat (x * y⁻¹) hne hx
    exact mul_inv_eq_one.mp h1
  have hΓcard : Nat.card ↥(rhoT_ba3s N).range = 3 := by
    have he : ↥(twoResidual N) ≃ ↥(rhoT_ba3s N).range :=
      (MulEquiv.ofBijective (rhoT_ba3s N).rangeRestrict
        ⟨(rhoT_ba3s N).rangeRestrict_injective_iff.mpr hρinj,
          (rhoT_ba3s N).rangeRestrict_surjective⟩).toEquiv
    exact (Nat.card_congr he).symm.trans hTcard
  have : Nontrivial ↥(commV N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hU4]; norm_num)
  have hirr := hirr_rhoT_ba3s hN hfpf hU4
  obtain ⟨π, hπinj, hπRV⟩ :=
    CFSG.QuasithinUnique.L246.exists_altDn_three (S := ↥(commV N)) hU2
      (rhoT_ba3s N).range hΓcard hirr
  obtain ⟨π', hπ'RV⟩ := transport_ba3s hρinj hπRV
  exact ⟨π', by rw [hcommV, hker]; exact hπ'RV⟩

theorem isAlt_three_and_realizes_altDn_three {W : Type} [CommGroup W] [Finite W]
    {N : Subgroup (MulAut W)} (hN : IsSLn ↥N 2 1) (hnat : BinaryNaturalSL N (commV N) ⊥ 2 1) :
    IsAlt ↥(twoResidual N) 3 ∧
      (FFModel.altDn 3).Realizes (twoResidual N) (commV (twoResidual N))
        (gomiWXKer (twoResidual N)) :=
  ⟨isAlt_three_of_isSLn_ba3s hN, realizes_altDn_three_ba3s hN hnat⟩

end CFSG.GroupTheory
