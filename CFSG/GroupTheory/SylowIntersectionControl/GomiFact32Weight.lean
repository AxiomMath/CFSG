module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePiecesAux
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

namespace CFSG.GroupTheory

open CFSG.Quasithin

public section

variable {H : Type} [CommGroup H] [Finite H]

private def fixOf {E : Type*} [Group E] (k : MulAut E) : Subgroup E where
  carrier := {e | k e = e}
  one_mem' := map_one k
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private lemma mem_fixOf {E : Type*} [Group E] {k : MulAut E} {e : E} :
    e ∈ fixOf k ↔ k e = e := Iff.rfl

private theorem card_fixOf_eq_two {E : Type*} [CommGroup E] [Finite E]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hEcard : Nat.card E = 4)
    {k : MulAut E} (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) :
    Nat.card (fixOf k) = 2 := by
  have hk2e : ∀ e : E, k (k e) = e := by
    intro e
    have h := congrArg (fun f : MulAut E => f e) hk2
    simpa [pow_two, MulAut.mul_apply] using h
  have hex : ∃ e : E, e ≠ 1 ∧ k e = e := by
    by_contra hcon
    have hkne : ∃ e : E, k e ≠ e := by
      by_contra h
      push Not at h
      exact hk1 (MulEquiv.ext h)
    obtain ⟨e, he⟩ := hkne
    have he1 : e ≠ 1 := by
      rintro rfl
      exact he (map_one k)
    have hee : e * e = 1 := by
      simpa [pow_two] using hE2 e
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    have hprod : e * k e ≠ 1 := by
      intro h
      apply he
      rw [show k e = e⁻¹ * (e * k e) by group, h, mul_one, heinv]
    have hfix : k (e * k e) = e * k e := by
      rw [map_mul, hk2e e]
      exact mul_comm (k e) e
    exact hcon ⟨e * k e, hprod, hfix⟩
  obtain ⟨e, he1, hefix⟩ := hex
  have hdvd : Nat.card (fixOf k) ∣ 4 := by
    have h := Subgroup.card_subgroup_dvd_card (fixOf k)
    rwa [hEcard] at h
  have hne1 : Nat.card (fixOf k) ≠ 1 := by
    intro h
    have hbot : fixOf k = ⊥ := Subgroup.eq_bot_of_card_eq (fixOf k) h
    have : e ∈ (⊥ : Subgroup E) := by rw [← hbot]; exact hefix
    rw [Subgroup.mem_bot] at this
    exact he1 this
  have hne4 : Nat.card (fixOf k) ≠ 4 := by
    intro h
    have htop : fixOf k = ⊤ := Subgroup.eq_top_of_card_eq (fixOf k) (h.trans hEcard.symm)
    apply hk1
    ext x
    have hx : x ∈ fixOf k := by rw [htop]; exact Subgroup.mem_top x
    exact hx
  have hle : Nat.card (fixOf k) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases Nat.card (fixOf k) <;> simp_all

private def nonidentityPerm {E : Type*} [Group E] :
    MulAut E →* Equiv.Perm {x : E // x ≠ 1} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (by
    intro x
    constructor
    · intro h hx
      exact h (hx ▸ map_one a)
    · intro hx hax
      apply hx
      apply a.injective
      simpa using hax)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

private lemma nonidentityPerm_injective {E : Type*} [Group E] :
    Function.Injective (nonidentityPerm (E := E)) := by
  intro a b hab
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val
      (congrArg (fun p : Equiv.Perm {x : E // x ≠ 1} => p ⟨x, hx⟩) hab)

private def permFinOf {E : Type*} [Group E] (e : {x : E // x ≠ 1} ≃ Fin 3) :
    MulAut E →* Equiv.Perm (Fin 3) :=
  e.permCongrHom.toMonoidHom.comp nonidentityPerm

private lemma permFinOf_injective {E : Type*} [Group E]
    (e : {x : E // x ≠ 1} ≃ Fin 3) :
    Function.Injective (permFinOf e) :=
  e.permCongrHom.injective.comp nonidentityPerm_injective

private lemma perm_fin_three_commuting_involutions_eq :
    ∀ p q : Equiv.Perm (Fin 3), p ^ 2 = 1 → q ^ 2 = 1 → p * q = q * p →
      p ≠ 1 → q ≠ 1 → p = q := by
  decide

private theorem elemAbelian2_hex_uniqueness
    {E : Type*} [CommGroup E] [Finite E]
    (_hE2 : ∀ e : E, e ^ 2 = 1) (hEcard : Nat.card E = 4)
    {K : Subgroup (MulAut E)} (hK : IsElemAbelian2 K) :
    (K ≠ ⊥ → ∃ k ∈ K, k ≠ 1) ∧
      (∀ k ∈ K, k ≠ 1 → ∀ l ∈ K, l ≠ 1 → k = l) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  have hEcard' : Fintype.card E = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hEcard
  have hXcard : Fintype.card {x : E // x ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl (fun x : E => x = 1)]
    simp [hEcard']
  let e : {x : E // x ≠ 1} ≃ Fin 3 := Fintype.equivFinOfCardEq hXcard
  let p : MulAut E →* Equiv.Perm (Fin 3) := permFinOf e
  have hp_inj : Function.Injective p := permFinOf_injective e
  have hex : K ≠ ⊥ → ∃ k ∈ K, k ≠ 1 := by
    intro hbot
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hx1 (h x hx)
  have huniq : ∀ k ∈ K, k ≠ 1 → ∀ l ∈ K, l ≠ 1 → k = l := by
    intro k hk hk1 l hl hl1
    have hpk2 : p k ^ 2 = 1 := by
      rw [← map_pow, hK.2 k hk, map_one]
    have hpl2 : p l ^ 2 = 1 := by
      rw [← map_pow, hK.2 l hl, map_one]
    have hcomm : p k * p l = p l * p k := by
      rw [← map_mul, ← map_mul, hK.1 k hk l hl]
    have hpk1 : p k ≠ 1 := fun h => hk1 (hp_inj (by rw [h, map_one]))
    have hpl1 : p l ≠ 1 := fun h => hl1 (hp_inj (by rw [h, map_one]))
    exact hp_inj
      (perm_fin_three_commuting_involutions_eq (p k) (p l) hpk2 hpl2 hcomm hpk1 hpl1)
  exact ⟨hex, huniq⟩

private theorem card_le_two_of_elemAbelian2_le_mulAut
    {E : Type*} [CommGroup E] [Finite E]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hEcard : Nat.card E = 4)
    {K : Subgroup (MulAut E)} (hK : IsElemAbelian2 K) :
    Nat.card K ≤ 2 := by
  classical
  obtain ⟨hex, huniq⟩ := elemAbelian2_hex_uniqueness hE2 hEcard hK
  by_cases hbot : K = ⊥
  · rw [hbot, Subgroup.card_bot]; norm_num
  · obtain ⟨k, hk, hk1⟩ := hex hbot
    have hKeq : K = Subgroup.zpowers k := by
      apply le_antisymm
      · intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]; exact Subgroup.one_mem _
        · rw [huniq x hx hx1 k hk hk1]
          exact Subgroup.mem_zpowers k
      · exact Subgroup.zpowers_le.mpr hk
    rw [hKeq, Nat.card_zpowers, orderOf_eq_prime (hK.2 k hk) hk1]

private theorem card_mul_card_fixV_eq_four_of_elemAbelian2_le_mulAut
    {E : Type*} [CommGroup E] [Finite E]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hEcard : Nat.card E = 4)
    {K : Subgroup (MulAut E)} (hK : IsElemAbelian2 K) :
    Nat.card K * Nat.card (fixV K) = 4 := by
  classical
  obtain ⟨hex, huniq⟩ := elemAbelian2_hex_uniqueness hE2 hEcard hK
  by_cases hbot : K = ⊥
  · rw [hbot, Subgroup.card_bot]
    have htop : fixV (⊥ : Subgroup (MulAut E)) = ⊤ := by
      ext x
      simp [mem_fixV]
    rw [htop, Subgroup.card_top, hEcard]
  · obtain ⟨k, hk, hk1⟩ := hex hbot
    have hKeq : K = Subgroup.zpowers k := by
      apply le_antisymm
      · intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]; exact Subgroup.one_mem _
        · rw [huniq x hx hx1 k hk hk1]
          exact Subgroup.mem_zpowers k
      · exact Subgroup.zpowers_le.mpr hk
    have hcardK : Nat.card K = 2 := by
      rw [hKeq, Nat.card_zpowers, orderOf_eq_prime (hK.2 k hk) hk1]
    have hfixK : fixV K = fixOf k := by
      ext x
      rw [mem_fixV, mem_fixOf]
      constructor
      · intro hx
        exact hx k hk
      · intro hx y hy
        by_cases hy1 : y = 1
        · rw [hy1, MulAut.one_apply]
        · rw [huniq y hy hy1 k hk hk1, hx]
    rw [hcardK, hfixK, card_fixOf_eq_two hE2 hEcard (hK.2 k hk) hk1]

private theorem card_mul_card_fixV_of_elemAbelian2_le_mulAut
    {E : Type*} [CommGroup E] [Finite E]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hEcard : Nat.card E = 4)
    {K : Subgroup (MulAut E)} (hK : IsElemAbelian2 K) :
    Nat.card K ≤ 2 ∧ Nat.card K * Nat.card (fixV K) = 4 :=
  ⟨card_le_two_of_elemAbelian2_le_mulAut hE2 hEcard hK,
    card_mul_card_fixV_eq_four_of_elemAbelian2_le_mulAut hE2 hEcard hK⟩

end

section

variable {H : Type} [CommGroup H]

private theorem famComm {I : Type*} [Fintype I] (V : I → Subgroup H) :
    Pairwise fun i j => ∀ x y : H, x ∈ V i → y ∈ V j → Commute x y :=
  fun _ _ _ x y _ _ => Commute.all x y

private noncomputable def famHom {I : Type*} [Fintype I] (V : I → Subgroup H) :
    (∀ i, V i) →* H :=
  Subgroup.noncommPiCoprod (H := V) (famComm V)

private theorem famHom_injective {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hind : iSupIndep V) : Function.Injective (famHom V) :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := famComm V) hind

private theorem famHom_apply {I : Type*} [Fintype I] {V : I → Subgroup H}
    (u : ∀ i, V i) : famHom V u = ∏ i, (u i : H) := by
  change Subgroup.noncommPiCoprod (famComm V) u = ∏ i, (u i : H)
  rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]

private theorem famHom_surjective {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hsup : ⨆ i, V i = ⊤) : Function.Surjective (famHom V) := by
  intro x
  have hx : x ∈ (famHom V).range := by
    rw [show (famHom V).range = ⨆ i, V i from
      Subgroup.noncommPiCoprod_range (hcomm := famComm V), hsup]
    exact Subgroup.mem_top x
  exact MonoidHom.mem_range.mp hx

private noncomputable def famComp {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hsup : ⨆ i, V i = ⊤) (x : H) (i : I) : V i :=
  Classical.choose (famHom_surjective hsup x) i

private theorem famComp_spec {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hsup : ⨆ i, V i = ⊤) (x : H) :
    famHom V (fun i => famComp hsup x i) = x :=
  Classical.choose_spec (famHom_surjective hsup x)

private theorem famComp_injective {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hsup : ⨆ i, V i = ⊤) {x y : H}
    (h : ∀ i, famComp hsup x i = famComp hsup y i) : x = y := by
  rw [← famComp_spec hsup x, ← famComp_spec hsup y]
  congr 1
  exact funext h

private theorem famComp_smul {I : Type*} [Fintype I] {V : I → Subgroup H}
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤)
    {a : MulAut H} (σ : I ≃ I) (hσ : ∀ i, (V i).map a.toMonoidHom = V (σ i))
    (x : H) (i : I) :
    ((famComp hsup (a x) (σ i) : V (σ i)) : H) = a ((famComp hsup x i : V i) : H) := by
  classical
  let u : ∀ j, V j := fun j =>
    ⟨a ((famComp hsup x (σ.symm j) : V (σ.symm j)) : H), by
      have hmem : ((famComp hsup x (σ.symm j) : V (σ.symm j)) : H) ∈ V (σ.symm j) :=
        (famComp hsup x (σ.symm j)).2
      have hmap : a ((famComp hsup x (σ.symm j) : V (σ.symm j)) : H) ∈
          (V (σ.symm j)).map a.toMonoidHom :=
        Subgroup.mem_map_of_mem a.toMonoidHom hmem
      rw [hσ (σ.symm j), σ.apply_symm_apply] at hmap
      exact hmap⟩
  have hu : famHom V u = a x := by
    rw [famHom_apply]
    have hreindex : (∏ j, (u j : H)) =
        ∏ k, a ((famComp hsup x k : V k) : H) := by
      refine Fintype.prod_equiv σ.symm (fun j => (u j : H))
        (fun k => a ((famComp hsup x k : V k) : H)) (fun j => ?_)
      simp only [u]
    have hx' : a x = ∏ k, a ((famComp hsup x k : V k) : H) := by
      calc a x = a (famHom V (fun k => famComp hsup x k)) := by rw [famComp_spec]
        _ = a (∏ k, (famComp hsup x k : H)) := by rw [famHom_apply]
        _ = ∏ k, a ((famComp hsup x k : V k) : H) := by rw [map_prod]
    rw [hreindex, hx']
  have hcomp : famComp hsup (a x) = u := by
    apply famHom_injective hind
    rw [famComp_spec, hu]
  exact congrArg (fun f : ∀ j, V j => ((f (σ i) : V (σ i)) : H)) hcomp |>.trans
    (by simp only [u]; rw [Equiv.symm_apply_apply])

end

public section

variable {H : Type} [CommGroup H] [Finite H]

private noncomputable def restrictMulAut {G : Type*} [Group G] (a : MulAut G)
    (U : Subgroup G) (hU : U.map a.toMonoidHom = U) : MulAut U where
  toFun x := ⟨a x.1, by
    have hx : a x.1 ∈ U.map a.toMonoidHom := Subgroup.mem_map_of_mem a.toMonoidHom x.2
    rwa [hU] at hx⟩
  invFun x := ⟨a⁻¹ x.1, by
    have hU' : U.map (a⁻¹).toMonoidHom = U := by
      have hcomp : (a⁻¹).toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
        ext y
        simp
      calc U.map (a⁻¹).toMonoidHom
          = (U.map a.toMonoidHom).map (a⁻¹).toMonoidHom := by rw [hU]
        _ = U.map ((a⁻¹).toMonoidHom.comp a.toMonoidHom) := by rw [Subgroup.map_map]
        _ = U.map (MonoidHom.id G) := by rw [hcomp]
        _ = U := Subgroup.map_id U
    have hx : a⁻¹ x.1 ∈ U.map (a⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (a⁻¹).toMonoidHom x.2
    rwa [hU'] at hx⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [map_mul]

private lemma finset_prod_lt_prod_of_pos {ι : Type*} [Fintype ι] {f g : ι → ℕ}
    (hpos : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i) {j : ι} (hlt : f j < g j) :
    (∏ i, f i) < ∏ i, g i := by
  classical
  set s := (Finset.univ : Finset ι).erase j with hs
  have hj : j ∉ s := Finset.notMem_erase j _
  have huniv : (Finset.univ : Finset ι) = insert j s := by
    rw [hs, Finset.insert_erase (Finset.mem_univ j)]
  rw [huniv, Finset.prod_insert hj, Finset.prod_insert hj]
  have hFpos : 0 < ∏ i ∈ s, f i := Finset.prod_pos (fun i _ => hpos i)
  have hFle : (∏ i ∈ s, f i) ≤ ∏ i ∈ s, g i :=
    Finset.prod_le_prod (fun i _ => hle i)
  have hgjpos : 0 < g j := lt_of_lt_of_le (hpos j) (hle j)
  calc f j * (∏ i ∈ s, f i) < g j * (∏ i ∈ s, f i) :=
        Nat.mul_lt_mul_of_pos_right hlt hFpos
    _ ≤ g j * (∏ i ∈ s, g i) := Nat.mul_le_mul_left _ hFle

private lemma four_mul_le_four_pow : ∀ n : ℕ, 1 ≤ n → 4 * n ≤ 4 ^ n
  | 0, h => by omega
  | 1, _ => by norm_num
  | n + 2, _ => by
      have ih : 4 * (n + 1) ≤ 4 ^ (n + 1) := four_mul_le_four_pow (n + 1) (by omega)
      have hpos : 0 < 4 ^ (n + 1) := pow_pos (by norm_num) _
      calc 4 * (n + 2) = 4 * (n + 1) + 4 := by ring
        _ ≤ 4 ^ (n + 1) + 4 := by omega
        _ ≤ 4 ^ (n + 1) + 3 * 4 ^ (n + 1) := by
            have : 4 ≤ 3 * 4 ^ (n + 1) := by nlinarith
            omega
        _ = 4 * 4 ^ (n + 1) := by ring
        _ = 4 ^ (n + 2) := by ring

private lemma four_mul_lt_four_pow : ∀ n : ℕ, 2 ≤ n → 4 * n < 4 ^ n
  | 0, h => by omega
  | 1, h => by omega
  | n + 2, _ => by
      have ih : 4 * (n + 1) ≤ 4 ^ (n + 1) := four_mul_le_four_pow (n + 1) (by omega)
      have hpos : 0 < 4 ^ (n + 1) := pow_pos (by norm_num) _
      calc 4 * (n + 2) = 4 * (n + 1) + 4 := by ring
        _ ≤ 4 ^ (n + 1) + 4 := by omega
        _ < 4 ^ (n + 1) + 3 * 4 ^ (n + 1) := by
            have : 4 < 3 * 4 ^ (n + 1) := by nlinarith
            omega
        _ = 4 * 4 ^ (n + 1) := by ring
        _ = 4 ^ (n + 2) := by ring

private lemma four_mul_eq_four_pow {n : ℕ} (h : 4 * n = 4 ^ n) : n = 1 := by
  rcases n with _ | _ | n
  · simp at h
  · rfl
  · exfalso
    exact (ne_of_lt (four_mul_lt_four_pow (n + 2) (by omega))) h

private lemma prod_four_mul_le_four_pow_sum {ι : Type} [Fintype ι] (o : ι → ℕ)
    (hpos : ∀ ω, 1 ≤ o ω) :
    (∏ ω, 4 * o ω) ≤ 4 ^ ∑ ω, o ω := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun ω _ => four_mul_le_four_pow _ (hpos ω)

private lemma eq_one_of_prod_four_mul_eq_four_pow_sum {ι : Type} [Fintype ι] (o : ι → ℕ)
    (hpos : ∀ ω, 1 ≤ o ω) (h : (∏ ω, 4 * o ω) = 4 ^ ∑ ω, o ω) :
    ∀ ω, o ω = 1 := by
  have hle : ∀ ω, 4 * o ω ≤ 4 ^ o ω := fun ω => four_mul_le_four_pow _ (hpos ω)
  have hprod : ∀ ω, 4 * o ω = 4 ^ o ω := by
    intro ω
    by_contra hne
    have hlt : 4 * o ω < 4 ^ o ω := lt_of_le_of_ne (hle ω) hne
    have hstrict := finset_prod_lt_prod_of_pos (f := fun ω => 4 * o ω)
      (g := fun ω => 4 ^ o ω) (fun i => by have := hpos i; omega) hle hlt
    rw [h, ← Finset.prod_pow_eq_pow_sum] at hstrict
    exact (lt_irrefl _) hstrict
  intro ω
  exact four_mul_eq_four_pow (hprod ω)

private noncomputable def permI {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j) (a : ↥A) (i : I) : I :=
  Classical.choose (hperm a.1 a.2 i)

omit [Finite H] in
private theorem permI_spec {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j) (a : ↥A) (i : I) :
    (V i).map a.1.toMonoidHom = V (permI hperm a i) :=
  Classical.choose_spec (hperm a.1 a.2 i)

omit [Finite H] in
private theorem permI_unique {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j)
    (hVinj : Function.Injective V) (a : ↥A) {i j : I}
    (h : (V i).map a.1.toMonoidHom = V j) : permI hperm a i = j := by
  apply hVinj
  rw [← permI_spec hperm a i, h]

omit [Finite H] in
private theorem permI_one {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j)
    (hVinj : Function.Injective V) (i : I) : permI hperm 1 i = i := by
  apply permI_unique hperm hVinj
  have h1 : ((1 : ↥A) : MulAut H) = 1 := rfl
  rw [h1]
  have hid : (1 : MulAut H).toMonoidHom = MonoidHom.id H := by
    rw [MulAut.one_def]
    exact MulEquiv.toMonoidHom_refl
  rw [hid]
  exact Subgroup.map_id (V i)

omit [Finite H] in
private theorem permI_mul {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j)
    (hVinj : Function.Injective V) (a b : ↥A) (i : I) :
    permI hperm (a * b) i = permI hperm a (permI hperm b i) := by
  apply permI_unique hperm hVinj
  have hmul : ((a * b : ↥A).1 : MulAut H).toMonoidHom =
      (a.1.toMonoidHom).comp (b.1.toMonoidHom) := by
    ext x
    simp [MulAut.mul_apply]
  rw [hmul, ← Subgroup.map_map, permI_spec hperm b i,
    permI_spec hperm a (permI hperm b i)]

@[instance_reducible]
private noncomputable def permAction {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hVinj : Function.Injective V)
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j) : MulAction ↥A I where
  smul a i := permI hperm a i
  one_smul i := permI_one hperm hVinj i
  mul_smul a b i := permI_mul hperm hVinj a b i

omit [Finite H] in
private theorem permAction_spec {I : Type} {V : I → Subgroup H} {A : Subgroup (MulAut H)}
    (hVinj : Function.Injective V)
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j) (a : ↥A) (i : I) :
    letI := permAction hVinj hperm
    (V i).map a.1.toMonoidHom = V (a • i) :=
  permI_spec hperm a i

section OrbitData

variable {I : Type} [Fintype I] {V : I → Subgroup H} {A : Subgroup (MulAut H)}
variable [MulAction ↥A I]

local notation "Ω" => MulAction.orbitRel.Quotient A I

private def mkq (A : Subgroup (MulAut H)) [MulAction ↥A I] (i : I) :
    MulAction.orbitRel.Quotient ↥A I :=
  Quotient.mk (MulAction.orbitRel ↥A I) i

private noncomputable def rep (ω : Ω) : I := Quotient.out ω

private def O (ω : Ω) : Type := ↥(MulAction.orbit ↥A (rep ω))

private noncomputable def W (V : I → Subgroup H) (ω : Ω) : Subgroup H := ⨆ i : O ω, V i.1

private noncomputable def K (ω : Ω) : Subgroup ↥A :=
  MulAction.stabilizer ↥A (rep ω)

private noncomputable def N (V : I → Subgroup H) (ω : Ω) : Subgroup ↥A :=
  fixingSubgroup ↥A (W V ω : Set H)

private def smulEquiv (a : ↥A) : I ≃ I where
  toFun i := a • i
  invFun i := a⁻¹ • i
  left_inv i := by
    change a⁻¹ • (a • i) = i
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv i := by
    change a • (a⁻¹ • i) = i
    rw [← mul_smul, mul_inv_cancel, one_smul]

private noncomputable def restrictHom
    (hσ : ∀ (a : ↥A) (i : I), (V i).map a.1.toMonoidHom = V (a • i))
    (ω : Ω) : K ω →* MulAut ↥(V (rep ω)) where
  toFun k := restrictMulAut k.1.1 (V (rep ω)) (by
    rw [hσ k.1 (rep ω), MulAction.mem_stabilizer_iff.mp k.2])
  map_one' := by
    ext x
    rfl
  map_mul' := fun k l => by
    ext x
    rfl

private noncomputable def Kbar
    (hσ : ∀ (a : ↥A) (i : I), (V i).map a.1.toMonoidHom = V (a • i))
    (ω : Ω) : Subgroup (MulAut ↥(V (rep ω))) :=
  (restrictHom hσ ω).range

private noncomputable instance instFintypeOrbitQuot : Fintype Ω := by
  classical
  exact Fintype.ofSurjective (Quotient.mk (MulAction.orbitRel ↥A I)) Quotient.exists_rep

private noncomputable instance instFintypeOrbit (ω : Ω) : Fintype (O ω) :=
  Fintype.ofFinite (α := ↥(MulAction.orbit ↥A (rep ω)))

omit [Finite H] [Fintype I] in
private theorem smul_unique (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hVinj : Function.Injective V) (a : ↥A) {i j : I}
    (h : (V i).map a.1.toMonoidHom = V j) : a • i = j := by
  apply hVinj
  rw [← hact a i, h]

omit [Finite H] [Fintype I] in
private theorem N_le_K (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hVinj : Function.Injective V) (ω : Ω) : N V ω ≤ K ω := by
  intro a ha
  change a ∈ fixingSubgroup ↥A (W V ω : Set H) at ha
  rw [mem_fixingSubgroup_iff] at ha
  have hfixV : ∀ x ∈ V (rep ω), ((a : ↥A).1 : MulAut H) x = x := by
    intro x hx
    have hxW : x ∈ W V ω :=
      le_iSup (fun i : O ω => V i.1) ⟨rep ω, MulAction.mem_orbit_self _⟩ hx
    have h := ha x hxW
    simpa [Subgroup.smul_def] using h
  apply smul_unique hact hVinj a
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change ((a : ↥A).1 : MulAut H) y ∈ V (rep ω)
    rw [hfixV y hy]
    exact hy
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx, hfixV x hx⟩

omit [Finite H] [Fintype I] in
private theorem restrictHom_ker_le (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i)) (hA : IsElemAbelian2 A) (ω : Ω) :
    (restrictHom hact ω).ker ≤ (N V ω).subgroupOf (K ω) := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  rw [Subgroup.mem_subgroupOf]
  change (k : ↥A) ∈ fixingSubgroup ↥A (W V ω : Set H)
  rw [mem_fixingSubgroup_iff]
  have hkV : ∀ v : ↥(V (rep ω)), k.1.1 (v : H) = (v : H) := by
    intro v
    have h1 : (restrictHom hact ω k) v = v := by
      rw [hk]
      rfl
    have h2 := congrArg Subtype.val h1
    simpa [restrictHom, restrictMulAut] using h2
  intro x hx
  refine Subgroup.iSup_induction (C := fun z : H => k.1.1 z = z)
    (fun i : O ω => V i.1) hx ?_ ?_ ?_
  · intro i v hv
    have hi : i.1 ∈ MulAction.orbit ↥A (rep ω) := i.2
    rw [MulAction.mem_orbit_iff] at hi
    obtain ⟨a, ha⟩ := hi
    have ha' : (smulEquiv a) (rep ω) = i.1 := by
      simpa [smulEquiv] using ha
    have hv' : v ∈ (V (rep ω)).map a.1.toMonoidHom := by
      rw [hact a (rep ω), ha]
      exact hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv'
    calc k.1.1 (a.1 w) = (k.1.1 * a.1) w := by rw [MulAut.mul_apply]
      _ = (a.1 * k.1.1) w := by rw [hA.1 k.1.1 k.1.2 a.1 a.2]
      _ = a.1 (k.1.1 w) := by rw [MulAut.mul_apply]
      _ = a.1 w := by rw [hkV ⟨w, hw⟩]
  · exact map_one k.1.1
  · intro x y hx hy
    rw [map_mul, hx, hy]

omit [Finite H] [Fintype I] in
private theorem restrictHom_ker_ge (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i)) (ω : Ω) :
    (N V ω).subgroupOf (K ω) ≤ (restrictHom hact ω).ker := by
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  change (k : ↥A) ∈ fixingSubgroup ↥A (W V ω : Set H) at hk
  rw [mem_fixingSubgroup_iff] at hk
  rw [MonoidHom.mem_ker]
  ext v
  have hvW : (v : H) ∈ W V ω :=
    le_iSup (fun i : O ω => V i.1) ⟨rep ω, MulAction.mem_orbit_self _⟩ v.2
  have hfix := hk (v : H) hvW
  have hfix' : k.1.1 (v : H) = (v : H) := by
    simpa [Subgroup.smul_def] using hfix
  simpa [restrictHom, restrictMulAut] using hfix'

omit [Finite H] [Fintype I] in
private theorem restrictHom_ker (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i)) (hA : IsElemAbelian2 A) (ω : Ω) :
    (restrictHom hact ω).ker = (N V ω).subgroupOf (K ω) :=
  le_antisymm (restrictHom_ker_le hact hA ω) (restrictHom_ker_ge hact ω)

omit [Finite H] [Fintype I] in
private theorem mem_orbit_rep (i : I) : i ∈ MulAction.orbit ↥A (rep (A := A) (mkq A i)) := by
  have hq : mkq A i = mkq A (rep (A := A) (mkq A i)) := by
    change Quotient.mk (MulAction.orbitRel ↥A I) i =
      Quotient.mk (MulAction.orbitRel ↥A I) (Quotient.out (mkq A i))
    exact (Quotient.out_eq' (mkq A i)).symm
  rw [← MulAction.orbitRel_apply]
  exact Quotient.exact hq

omit [Finite H] [Fintype I] in
private theorem isElemAbelian2_Kbar (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i)) (hA : IsElemAbelian2 A) (ω : Ω) :
    IsElemAbelian2 (Kbar hact ω) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hA.1 k.1.1 k.1.2 l.1.1 l.1.2
  · rintro _ ⟨k, rfl⟩
    rw [← map_pow]
    have hk2 : k ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hA.2 k.1.1 k.1.2
    rw [hk2, map_one]

omit [Fintype I] in
private theorem card_Kbar (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hH2 : ∀ h : H, h ^ 2 = 1) (hcard : ∀ i, Nat.card (V i) = 4)
    (hA : IsElemAbelian2 A) (ω : Ω) :
    Nat.card (Kbar hact ω) ≤ 2 ∧
      Nat.card (Kbar hact ω) * Nat.card (fixV (Kbar hact ω)) = 4 :=
  card_mul_card_fixV_of_elemAbelian2_le_mulAut
    (fun e : ↥(V (rep ω)) => Subtype.ext (hH2 (e : H))) (hcard (rep ω))
    (isElemAbelian2_Kbar hact hA ω)

omit [Finite H] [Fintype I] in
private theorem iInf_N_eq_bot (hsup : ⨆ i, V i = ⊤) : (⨅ ω : Ω, N V ω) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have haW : ∀ ω, a ∈ N V ω := fun ω => Subgroup.mem_iInf.mp ha ω
  apply Subtype.ext
  ext x
  have hx : x ∈ ⨆ i, V i := by rw [hsup]; exact Subgroup.mem_top x
  refine Subgroup.iSup_induction (C := fun z : H => a.1 z = z) (fun i => V i) hx ?_ ?_ ?_
  · intro i y hy
    let ω : Ω := mkq A i
    have hyW : y ∈ W V ω :=
      le_iSup (fun j : O ω => V j.1) ⟨i, mem_orbit_rep (A := A) i⟩ hy
    have hfix := (mem_fixingSubgroup_iff (↥A)).mp (haW ω) y hyW
    simpa [Subgroup.smul_def] using hfix
  · exact map_one a.1
  · intro y z hy hz
    rw [map_mul, hy, hz]

private noncomputable def fixToProd (hsup : ⨆ i, V i = ⊤) :
    ↥(fixV A) → (∀ ω : Ω, ↥(V (rep ω))) :=
  fun x ω => famComp hsup (x : H) (rep ω)

omit [Finite H] in
private theorem fixToProd_mem (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) (ω : Ω)
    (x : ↥(fixV A)) : fixToProd hsup x ω ∈ fixV (Kbar hact ω) := by
  rw [mem_fixV]
  intro φ hφ
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hφ
  have hkx : k.1.1 ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H) =
      ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H) := by
    have hxfix : k.1.1 (x : H) = (x : H) := x.2 k.1.1 k.1.2
    have hσ := famComp_smul hind hsup (smulEquiv k.1) (fun i => hact k.1 i) (x : H)
      (rep ω)
    have hkrep : (smulEquiv k.1) (rep ω) = rep ω := by
      simpa [smulEquiv] using MulAction.mem_stabilizer_iff.mp k.2
    rw [hxfix, hkrep] at hσ
    exact hσ.symm
  rw [← hk]
  ext
  change k.1.1 ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H) =
    ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H)
  simpa [restrictHom, restrictMulAut] using hkx

omit [Finite H] in
private theorem fixToProd_injective (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) :
    Function.Injective (fixToProd (A := A) hsup) := by
  intro x y hxy
  apply Subtype.ext
  apply famComp_injective hsup
  intro i
  apply Subtype.ext
  let ω : Ω := mkq A i
  have hω : famComp hsup (x : H) (rep ω) = famComp hsup (y : H) (rep ω) := by
    simpa [fixToProd] using congrArg Subtype.val (congrFun hxy ω)
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (mem_orbit_rep (A := A) i)
  have ha' : (smulEquiv a) (rep ω) = i := by
    simpa [smulEquiv] using ha
  have hxi : ((famComp hsup (x : H) i : V i) : H) =
      a.1 ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H) := by
    have hσ := famComp_smul hind hsup (smulEquiv a) (fun i => hact a i) (x : H) (rep ω)
    rw [ha'] at hσ
    rw [show ((a : ↥A).1 : MulAut H) (x : H) = (x : H) from x.2 a.1 a.2] at hσ
    exact hσ
  have hyi : ((famComp hsup (y : H) i : V i) : H) =
      a.1 ((famComp hsup (y : H) (rep ω) : V (rep ω)) : H) := by
    have hσ := famComp_smul hind hsup (smulEquiv a) (fun i => hact a i) (y : H) (rep ω)
    rw [ha'] at hσ
    rw [show ((a : ↥A).1 : MulAut H) (y : H) = (y : H) from y.2 a.1 a.2] at hσ
    exact hσ
  calc ((famComp hsup (x : H) i : V i) : H)
      = a.1 ((famComp hsup (x : H) (rep ω) : V (rep ω)) : H) := hxi
    _ = a.1 ((famComp hsup (y : H) (rep ω) : V (rep ω)) : H) := by rw [hω]
    _ = ((famComp hsup (y : H) i : V i) : H) := hyi.symm

private theorem card_fixV_le_prod (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) :
    Nat.card (fixV A) ≤ ∏ ω : Ω, Nat.card (fixV (Kbar hact ω)) := by
  classical
  let f : ↥(fixV A) → (∀ ω : Ω, ↥(fixV (Kbar hact ω))) := fun x ω =>
    ⟨fixToProd hsup x ω, fixToProd_mem hact hind hsup ω x⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply fixToProd_injective hact hind hsup
    funext ω
    simpa [f, fixToProd] using congrArg Subtype.val (congrFun hxy ω)
  have h := Nat.card_le_card_of_injective f hf_inj
  rwa [Nat.card_pi] at h

omit [Finite H] in
private theorem isMulCommutative_of_isElemAbelian2 (hA : IsElemAbelian2 A) :
    IsMulCommutative ↥A :=
  ⟨⟨fun a b => Subtype.ext (hA.1 a.1 a.2 b.1 b.2)⟩⟩

omit [Finite H] [Fintype I] in
private theorem card_K_eq (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hA : IsElemAbelian2 A) (hVinj : Function.Injective V) (ω : Ω) :
    Nat.card (K ω) = Nat.card (N V ω) * Nat.card (Kbar hact ω) := by
  have hcard := Subgroup.card_ker_mul_card_range (restrictHom hact ω)
  rw [restrictHom_ker hact hA ω] at hcard
  have hNcard : Nat.card ↥((N V ω).subgroupOf (K ω)) = Nat.card (N V ω) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (N_le_K hact hVinj ω)).toEquiv
  rw [hNcard] at hcard
  exact hcard.symm

omit [Finite H] [Fintype I] in
private theorem card_O_mul_card_K (ω : Ω) :
    Nat.card (O ω) * Nat.card (K ω) = Nat.card ↥A := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := ↥A) (rep ω))
  rwa [Nat.card_prod] at h

omit [Fintype I] in
private theorem card_quotient_eq [IsMulCommutative ↥A] (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hA : IsElemAbelian2 A) (hVinj : Function.Injective V) (ω : Ω) :
    Nat.card (↥A ⧸ N V ω) = Nat.card (O ω) * Nat.card (Kbar hact ω) := by
  have hAeq : Nat.card (↥A ⧸ N V ω) * Nat.card (N V ω) = Nat.card ↥A :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (N V ω)).symm
  have hNpos : 0 < Nat.card (N V ω) := Nat.card_pos
  apply Nat.mul_right_cancel hNpos
  calc Nat.card (↥A ⧸ N V ω) * Nat.card (N V ω) = Nat.card ↥A := hAeq
    _ = Nat.card (O ω) * Nat.card (K ω) := (card_O_mul_card_K (A := A) ω).symm
    _ = Nat.card (O ω) * (Nat.card (N V ω) * Nat.card (Kbar hact ω)) := by
        rw [card_K_eq hact hA hVinj ω]
    _ = (Nat.card (O ω) * Nat.card (Kbar hact ω)) * Nat.card (N V ω) := by ring

private theorem card_le_prod (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hsup : ⨆ i, V i = ⊤) (hA : IsElemAbelian2 A) (hVinj : Function.Injective V) :
    Nat.card A ≤ ∏ ω : Ω, Nat.card (O ω) * Nat.card (Kbar hact ω) := by
  classical
  have := isMulCommutative_of_isElemAbelian2 (A := A) hA
  let q : ↥A →* (∀ ω : Ω, ↥A ⧸ N V ω) :=
    { toFun := fun a ω => QuotientGroup.mk' (N V ω) a
      map_one' := by
        ext ω
        rfl
      map_mul' := by
        intro a b
        ext ω
        rfl }
  have hq_ker : q.ker = ⨅ ω : Ω, N V ω := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_iInf]
    constructor
    · intro h ω
      have := congrFun h ω
      simpa [q] using (QuotientGroup.eq_one_iff (N := N V ω) a).mp this
    · intro h
      ext ω
      simpa [q] using (QuotientGroup.eq_one_iff (N := N V ω) a).mpr (h ω)
  have hq_inj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff q, hq_ker, iInf_N_eq_bot hsup]
  have h := Nat.card_le_card_of_injective q hq_inj
  rw [Nat.card_pi] at h
  refine h.trans_eq ?_
  apply Finset.prod_congr rfl
  intro ω _
  exact card_quotient_eq hact hA hVinj ω

omit [Finite H] in
private theorem card_I_eq_sum : Fintype.card I = ∑ ω : Ω, Fintype.card (O ω) := by
  classical
  have e : I ≃ (Σ ω : Ω, O ω) := by
    simpa [O, rep] using MulAction.selfEquivSigmaOrbits ↥A I
  calc Fintype.card I = Fintype.card (Σ ω : Ω, O ω) := Fintype.card_congr e
    _ = ∑ ω : Ω, Fintype.card (O ω) := Fintype.card_sigma

private theorem card_H_eq_four_pow (hcard : ∀ i, Nat.card (V i) = 4)
    (hsup : ⨆ i, V i = ⊤) (hind : iSupIndep V) :
    Nat.card H = 4 ^ Fintype.card I := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hcard' : ∀ i, Fintype.card (V i) = 4 := by
    intro i
    rw [← Nat.card_eq_fintype_card]
    exact hcard i
  rw [← Subgroup.card_top, ← hsup, CFSG.AGLEmbedding.card_iSup_eq_prod_of_iSupIndep hind]
  simp [hcard']

private theorem card_H_eq_prod (hcard : ∀ i, Nat.card (V i) = 4)
    (hsup : ⨆ i, V i = ⊤) (hind : iSupIndep V) :
    Nat.card H = ∏ ω : Ω, 4 ^ Nat.card (O ω) := by
  classical
  rw [card_H_eq_four_pow hcard hsup hind, card_I_eq_sum (A := A),
    ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro ω _
  rw [Nat.card_eq_fintype_card]

omit [Finite H] in
private theorem one_le_card_O (ω : Ω) : 1 ≤ Nat.card (O ω) := by
  have : Nonempty (O ω) := ⟨⟨rep ω, MulAction.mem_orbit_self _⟩⟩
  have := Nat.card_pos (α := O ω)
  omega

private theorem weight_le_prod (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hH2 : ∀ h : H, h ^ 2 = 1) (hcard : ∀ i, Nat.card (V i) = 4)
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) (hA : IsElemAbelian2 A)
    (hVinj : Function.Injective V) :
    Nat.card A * Nat.card (fixV A) ≤ ∏ ω : Ω, 4 * Nat.card (O ω) := by
  calc Nat.card A * Nat.card (fixV A)
      ≤ Nat.card A * ∏ ω : Ω, Nat.card (fixV (Kbar hact ω)) :=
        Nat.mul_le_mul_left _ (card_fixV_le_prod hact hind hsup)
    _ ≤ (∏ ω : Ω, Nat.card (O ω) * Nat.card (Kbar hact ω)) *
          ∏ ω : Ω, Nat.card (fixV (Kbar hact ω)) :=
        Nat.mul_le_mul_right _ (card_le_prod hact hsup hA hVinj)
    _ = ∏ ω : Ω, (Nat.card (O ω) * Nat.card (Kbar hact ω)) *
          Nat.card (fixV (Kbar hact ω)) :=
        Finset.prod_mul_distrib.symm
    _ = ∏ ω : Ω, 4 * Nat.card (O ω) := by
        apply Finset.prod_congr rfl
        intro ω _
        have hk := (card_Kbar hact hH2 hcard hA ω).2
        calc (Nat.card (O ω) * Nat.card (Kbar hact ω)) *
              Nat.card (fixV (Kbar hact ω))
            = Nat.card (O ω) * (Nat.card (Kbar hact ω) *
              Nat.card (fixV (Kbar hact ω))) := by ring
          _ = Nat.card (O ω) * 4 := by rw [hk]
          _ = 4 * Nat.card (O ω) := by ring

private theorem weight_le (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hH2 : ∀ h : H, h ^ 2 = 1) (hcard : ∀ i, Nat.card (V i) = 4)
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) (hA : IsElemAbelian2 A)
    (hVinj : Function.Injective V) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card H := by
  refine (weight_le_prod hact hH2 hcard hind hsup hA hVinj).trans ?_
  rw [card_H_eq_prod (A := A) hcard hsup hind, Finset.prod_pow_eq_pow_sum]
  exact prod_four_mul_le_four_pow_sum (fun ω : Ω => Nat.card (O ω)) (one_le_card_O (A := A))

private theorem map_eq_of_card_mul_eq (hact : ∀ (a : ↥A) (i : I),
      (V i).map a.1.toMonoidHom = V (a • i))
    (hH2 : ∀ h : H, h ^ 2 = 1) (hcard : ∀ i, Nat.card (V i) = 4)
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) (hA : IsElemAbelian2 A)
    (hVinj : Function.Injective V)
    (heq : Nat.card A * Nat.card (fixV A) = Nat.card H) :
    ∀ a ∈ A, ∀ i, (V i).map (MulEquiv.toMonoidHom a) = V i := by
  classical
  have hchain := weight_le_prod hact hH2 hcard hind hsup hA hVinj
  have hH := card_H_eq_prod (A := A) hcard hsup hind
  have hPQ : (∏ ω : Ω, 4 * Nat.card (O ω)) =
      ∏ ω : Ω, 4 ^ Nat.card (O ω) := by
    apply le_antisymm
    · rw [Finset.prod_pow_eq_pow_sum]
      exact prod_four_mul_le_four_pow_sum (fun ω : Ω => Nat.card (O ω))
        (one_le_card_O (A := A))
    · rw [← hH, ← heq]
      exact hchain
  have hPQ' : (∏ ω : Ω, 4 * Nat.card (O ω)) = 4 ^ ∑ ω : Ω, Nat.card (O ω) := by
    rw [hPQ, Finset.prod_pow_eq_pow_sum]
  have hsingle : ∀ ω : Ω, Nat.card (O ω) = 1 :=
    eq_one_of_prod_four_mul_eq_four_pow_sum (fun ω : Ω => Nat.card (O ω))
      (one_le_card_O (A := A)) hPQ'
  intro a ha i
  let a' : ↥A := ⟨a, ha⟩
  have horb_i : Nat.card ↥(MulAction.orbit ↥A i) = 1 := by
    rw [MulAction.orbit_eq_iff.mpr (mem_orbit_rep (A := A) i)]
    exact hsingle (mkq A i)
  have : Subsingleton ↥(MulAction.orbit ↥A i) :=
    (Nat.card_eq_one_iff_unique.mp horb_i).1
  have hmem : a' • i ∈ MulAction.orbit ↥A i := MulAction.mem_orbit _ _
  have haii : a' • i = i := by
    have h := Subsingleton.elim (⟨a' • i, hmem⟩ : ↥(MulAction.orbit ↥A i))
      ⟨i, MulAction.mem_orbit_self i⟩
    exact congrArg Subtype.val h
  rw [hact a' i, haii]

end OrbitData

theorem card_mul_card_fixV_le_of_perm
    (hH2 : ∀ h : H, h ^ 2 = 1)
    {I : Type} [Fintype I] (V : I → Subgroup H)
    (hind : iSupIndep V) (hsup : ⨆ i, V i = ⊤) (hcard : ∀ i, Nat.card (V i) = 4)
    {A : Subgroup (MulAut H)} (hA : IsElemAbelian2 A)
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (V i).map a.toMonoidHom = V j) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card H ∧
      (Nat.card A * Nat.card (fixV A) = Nat.card H →
        ∀ a ∈ A, ∀ i, (V i).map a.toMonoidHom = V i) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hVne : ∀ i, V i ≠ ⊥ := by
    intro i h
    have h4 := hcard i
    rw [h, Subgroup.card_bot] at h4
    omega
  have hVinj : Function.Injective V := hind.injective hVne
  let : MulAction ↥A I := permAction hVinj hperm
  have hact : ∀ (a : ↥A) (i : I), (V i).map a.1.toMonoidHom = V (a • i) :=
    permAction_spec hVinj hperm
  exact ⟨weight_le hact hH2 hcard hind hsup hA hVinj,
    fun heq => map_eq_of_card_mul_eq hact hH2 hcard hind hsup hA hVinj heq⟩

end

end CFSG.GroupTheory
