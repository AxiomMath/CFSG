module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers

namespace SPLMSide

theorem map_inf_centralizer_eq_centerOf {X : Type*} [Group X] {K : Subgroup X}
    (T : Subgroup K) :
    (T ⊓ Subgroup.centralizer (T : Set K)).map K.subtype = centerOf (T.map K.subtype) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyT, hyC⟩, rfl⟩
    refine ⟨⟨y, hyT, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, htT, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyC t htT)
  · rintro ⟨⟨y, hyT, rfl⟩, hxC⟩
    refine ⟨y, ⟨hyT, Subgroup.mem_centralizer_iff.mpr fun t htT => ?_⟩, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ ⟨t, htT, rfl⟩)

theorem coe_mem_normalizer_map_of_mem {X : Type*} [Group X] {K : Subgroup X} {T : Subgroup K}
    {b : K} (hb : b ∈ Subgroup.normalizer (T : Set K)) :
    (b : X) ∈ Subgroup.normalizer ((T.map K.subtype : Subgroup X) : Set X) :=
  Subgroup.le_normalizer_map K.subtype ⟨b, hb, rfl⟩

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem isPGroup_centralizer_of_isCyclic_inf (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} (hKn : K.Normal)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)) :
    IsPGroup p (Subgroup.centralizer (K : Set X)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzn : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  have : K.Normal := hKn
  have hK'n : (K ⊔ Subgroup.zpowers z).Normal := inferInstance
  have hCeq : Subgroup.centralizer ((K ⊔ Subgroup.zpowers z : Subgroup X) : Set X) =
      Subgroup.centralizer (K : Set X) := by
    refine le_antisymm (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)) ?_
    intro c hc
    have hcK : K ≤ Subgroup.centralizer (Subgroup.zpowers c : Set X) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hc)
    have hzc : Subgroup.zpowers z ≤ Subgroup.centralizer (Subgroup.zpowers c : Set X) :=
      (Subgroup.zpowers_le.mpr hz).trans (Subgroup.center_le_centralizer _)
    exact Subgroup.le_centralizer_iff.mpr (sup_le hcK hzc) (Subgroup.mem_zpowers c)
  rw [← hCeq]
  refine isPGroup_centralizer_of_forall_mem hp h.ne_two h.core_eq_bot hK'n ?_
  intro c hc hcp
  refine mem_of_mem_centralizer_of_orderOf_eq R hK'n ?_ hc hcp
  rintro c ⟨hcR, hcC⟩ hcp
  rw [hCeq] at hcC
  set C : Subgroup X := (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)
  have hzC : z ∈ C := ⟨mem_sylow_of_mem_center hz hzp R,
    Subgroup.mem_centralizer_iff.mpr fun y _ => (Subgroup.mem_center_iff.mp hz y)⟩
  have hcC' : c ∈ C := ⟨hcR, hcC⟩
  have heq : Subgroup.zpowers (⟨c, hcC'⟩ : C) = Subgroup.zpowers (⟨z, hzC⟩ : C) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hcp, hzp]
  have hmem : (⟨c, hcC'⟩ : C) ∈ Subgroup.zpowers (⟨z, hzC⟩ : C) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := hmem
  refine Subgroup.mem_sup_right ⟨k, ?_⟩
  simpa using congrArg Subtype.val hk

theorem isCyclic_centralizer_of_isCyclic_inf (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} (hKn : K.Normal)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)) :
    IsCyclic (Subgroup.centralizer (K : Set X)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : K.Normal := hKn
  have hle : Subgroup.centralizer (K : Set X) ≤
      (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) :=
    le_inf ((isPGroup_centralizer_of_isCyclic_inf h hz hzp hKn hcyc).le_sylow_of_normal R) le_rfl
  exact Subgroup.isCyclic_of_le hle

omit [Finite X] in
theorem mem_normalizer_of_mem_inf_coatom {K : Subgroup X} {T : Subgroup K}
    (hT : T.map K.subtype = (R : Subgroup X) ⊓ K)
    (hcoat : IsCoatom (Subgroup.normalizer (T : Set K)))
    (hN : K ⊓ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀)
    (hKX₀ : ¬ K ≤ X₀) {x : X} (hxK : x ∈ K) (hxX₀ : x ∈ X₀) :
    x ∈ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
  have hBY : Subgroup.normalizer (T : Set K) ≤ X₀.subgroupOf K := fun b hb =>
    Subgroup.mem_subgroupOf.mpr (hN ⟨b.2, hT ▸ coe_mem_normalizer_map_of_mem hb⟩)
  have hY : X₀.subgroupOf K = Subgroup.normalizer (T : Set K) := by
    by_contra hne
    refine hKX₀ fun y hy => ?_
    have htop := hcoat.2 _ (lt_of_le_of_ne hBY (Ne.symm hne))
    exact Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top (⟨y, hy⟩ : K))
  have hmem : (⟨x, hxK⟩ : K) ∈ Subgroup.normalizer (T : Set K) :=
    hY ▸ Subgroup.mem_subgroupOf.mpr hxX₀
  exact hT ▸ coe_mem_normalizer_map_of_mem hmem

omit [Finite X] in
theorem conj_mem_inf_of_coatom {K : Subgroup X} (hKn : K.Normal) {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hcoat : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K)))
    (hN : K ⊓ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀)
    (hKX₀ : ¬ K ≤ X₀) :
    ∀ x ∈ X₀, ∀ t ∈ (R : Subgroup X) ⊓ K, x * t * x⁻¹ ∈ (R : Subgroup X) ⊓ K := by
  intro x hx t ht
  set S : Subgroup X := (R : Subgroup X) ⊓ K
  have hSp : IsPGroup p S := R.isPGroup'.to_le inf_le_left
  have hSX₀ : S ≤ X₀ := fun y hy => hN ⟨hy.2, Subgroup.le_normalizer hy⟩
  set Q : Subgroup X := S.map (MulAut.conj x).toMonoidHom
  have hQ : ∀ q ∈ Q, q ∈ K ∧ q ∈ X₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hKn.conj_mem y hy.2 x, X₀.mul_mem (X₀.mul_mem hx (hSX₀ hy)) (X₀.inv_mem hx)⟩
  have hQN : Q ≤ Subgroup.normalizer (S : Set X) := fun q hq =>
    mem_normalizer_of_mem_inf_coatom hT hcoat hN hKX₀ (hQ q hq).1 (hQ q hq).2
  have hsup : IsPGroup p (Q ⊔ S : Subgroup X) := (hSp.map _).to_sup_of_normal_right' hSp hQN
  have hTle : (T : Subgroup K) ≤ (Q ⊔ S).comap K.subtype := fun y hy =>
    Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (hT ▸ ⟨y, hy, rfl⟩))
  have heq := T.is_maximal' hsup.comap_subtype hTle
  have htQ : x * t * x⁻¹ ∈ Q := ⟨t, ht, rfl⟩
  have hmem : (⟨x * t * x⁻¹, (hQ _ htQ).1⟩ : K) ∈ (Q ⊔ S).comap K.subtype :=
    Subgroup.mem_comap.mpr (Subgroup.mem_sup_left htQ)
  rw [heq] at hmem
  exact hT ▸ ⟨_, hmem, rfl⟩

omit [Finite X] in
theorem exists_pow_eq_one_of_commute [Fact p.Prime] {K : Subgroup X} (hKn : K.Normal)
    (hC : IsPGroup p (Subgroup.centralizer (K : Set X))) {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hinn : ∀ f : MulAut K, (∀ v ∈ (T : Subgroup K), f v = v) →
      ∃ t ∈ (T : Subgroup K), f = MulAut.conj t)
    {x : X} (hx : ∀ t ∈ (R : Subgroup X) ⊓ K, x * t = t * x) : ∃ k : ℕ, x ^ p ^ k = 1 := by
  have : K.Normal := hKn
  obtain ⟨t, htT, hft⟩ := hinn (MulAut.conjNormal x) fun v hv => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hx v (hT ▸ ⟨v, hv, rfl⟩), mul_inv_cancel_right]
  have hyC : (t : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hft ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc k * ((t : X)⁻¹ * x) = (t : X)⁻¹ * (t * k * (t : X)⁻¹) * x := by group
      _ = (t : X)⁻¹ * (x * k * x⁻¹) * x := by rw [h1]
      _ = (t : X)⁻¹ * x * k := by group
  obtain ⟨a, ha⟩ := hC ⟨_, hyC⟩
  obtain ⟨b, hb⟩ := T.isPGroup' ⟨t, htT⟩
  have hcomm : Commute (t : X) ((t : X)⁻¹ * x) := Subgroup.mem_centralizer_iff.mp hyC t t.2
  have ha' : ((t : X)⁻¹ * x) ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : (t : X) ^ p ^ b = 1 := by
    simpa using congrArg Subtype.val (congrArg Subtype.val hb)
  have h1 : (t : X) ^ p ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hb', one_pow]
  have h2 : ((t : X)⁻¹ * x) ^ p ^ (a + b) = 1 := by rw [pow_add, pow_mul, ha', one_pow]
  refine ⟨a + b, ?_⟩
  have hx' : x = (t : X) * ((t : X)⁻¹ * x) := by group
  rw [hx', hcomm.mul_pow, h1, h2, one_mul]

theorem isSolvable_of_conj_mem [Fact p.Prime] {K : Subgroup X} (hKn : K.Normal)
    (hC : IsPGroup p (Subgroup.centralizer (K : Set X))) {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hsolv : ∀ A : Subgroup (MulAut K),
      (∀ α ∈ A, (T : Subgroup K).map (α : K ≃* K).toMonoidHom = T) → Group.IsSolvable A)
    (hnorm : ∀ x ∈ X₀, ∀ t ∈ (R : Subgroup X) ⊓ K, x * t * x⁻¹ ∈ (R : Subgroup X) ⊓ K) :
    Group.IsSolvable X₀ := by
  have : K.Normal := hKn
  set φ : X₀ →* MulAut K := (MulAut.conjNormal (H := K)).comp X₀.subtype
  have hle : ∀ x ∈ X₀, (T : Subgroup K).map (MulAut.conjNormal x : K ≃* K).toMonoidHom ≤ T := by
    rintro x hx _ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hT.symm ▸ hnorm x hx v (hT ▸ ⟨v, hv, rfl⟩)
    have : w = MulAut.conjNormal x v := Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hwv)
    exact this ▸ hw
  have hA : ∀ α ∈ φ.range, (T : Subgroup K).map (α : K ≃* K).toMonoidHom = T := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge (hle x x.2)
      (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  have hsA : Group.IsSolvable φ.range := hsolv _ hA
  have hker : IsPGroup p φ.ker := by
    intro y
    have hyC : ((y : X₀) : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [← ker_conjNormal_eq_centralizer]
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp y.2)
    obtain ⟨k, hk⟩ := hC ⟨_, hyC⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have : Group.IsSolvable φ.ker := by
    have := hker.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem card_le_of_le_isCyclic (hp : p.Prime) {E C : Subgroup X} (hE : IsElemAbelian p E)
    (hEC : E ≤ C) (hC : IsCyclic C) : Nat.card E ≤ p := by
  have : IsCyclic E := Subgroup.isCyclic_of_le hEC
  exact card_le_of_isCyclic_of_forall_pow_eq_one hp.pos fun e =>
    Subtype.ext (by simpa using hE.2 e e.2)

theorem card_le_pow_five [Fact p.Prime] {K : Subgroup X} (hKn : K.Normal)
    (hcyc : IsCyclic (Subgroup.centralizer (K : Set X)))
    (hAut : ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E ≤ p ^ 4)
    {A : Subgroup X} (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 5 := by
  have hp : p.Prime := Fact.out
  have : K.Normal := hKn
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K A
  have h1 : Open.pRank p (A ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
    obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained p hp (A ⊓ Subgroup.centralizer (K : Set X))
    have hle := card_le_of_le_isCyclic hp hEel (hE.trans inf_le_right) hcyc
    rw [hEcard] at hle
    by_contra h2
    have h3 := Nat.pow_le_pow_right hp.pos (show 2 ≤ Open.pRank p
      (A ⊓ Subgroup.centralizer (K : Set X)) by omega)
    have h4 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have h4 : Open.pRank p (A.map (MulAut.conjNormal (H := K))) ≤ 4 := by
    obtain ⟨E, -, hEel, hEcard⟩ := pRank_attained p hp (A.map (MulAut.conjNormal (H := K)))
    have hle := hAut E hEel
    rw [hEcard] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hAp : IsPGroup p A := fun y => ⟨1, Subtype.ext (by simpa using hA.2 y y.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
  have hkle : k ≤ Open.pRank p A := le_csSup (pRank_bddAbove p hp A) ⟨A, le_rfl, hA, hk⟩
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end SPLMSide

end CFSG.AGLEmbedding
