module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.L32Facts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreQ
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenGroup
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem eq_of_sq_eq_one_of_isCyclic {T : Subgroup G} (hT : IsCyclic T) {u v : G} (hu : u ∈ T)
    (hv : v ∈ T) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  classical
  by_contra huv
  let _ : Fintype T := Fintype.ofFinite T
  have hle := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) (by norm_num)
  have hsub : ({1, ⟨u, hu⟩, ⟨v, hv⟩} : Finset T) ⊆ Finset.univ.filter (fun x : T => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · simp
    · exact Subtype.ext (by simpa [pow_two] using hu2)
    · exact Subtype.ext (by simpa [pow_two] using hv2)
  have hcard : ({1, ⟨u, hu⟩, ⟨v, hv⟩} : Finset T).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; exact huv (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hu1 (congrArg Subtype.val h).symm, fun h => hv1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_card hsub
  omega

theorem card_inf_le_two_of_isCyclic {T E : Subgroup G} (hT : IsCyclic T)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card (T ⊓ E : Subgroup G) ≤ 2 := by
  classical
  let _ : Fintype T := Fintype.ofFinite T
  have hle := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) (by norm_num)
  let f : (T ⊓ E : Subgroup G) → T := fun x => ⟨x, x.2.1⟩
  have hf : Function.Injective f := fun x y h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hrange : ∀ x, f x ∈ Finset.univ.filter (fun x : T => x ^ 2 = 1) := by
    intro x
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Subtype.ext (by simpa [pow_two, f] using hE x x.2.2)⟩
  let _ : Fintype (T ⊓ E : Subgroup G) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact (Finset.card_le_card_of_injOn f (fun x _ => hrange x) hf.injOn).trans hle

omit [Finite G] in
theorem mul_comm_of_isCyclic {T : Subgroup G} (hT : IsCyclic T) {u v : G} (hu : u ∈ T)
    (hv : v ∈ T) : u * v = v * u := by
  have h := (inferInstance : IsMulCommutative T).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
  exact congrArg Subtype.val h

omit [Finite G] in
theorem mul_self_mem_of_relIndex_eq_two {N T : Subgroup G} (h : T.relIndex N = 2) {x : G}
    (hx : x ∈ N) : x * x ∈ T :=
  Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two (H := T.subgroupOf N) h ⟨x, hx⟩)

omit [Finite G] in
theorem isSolvable_of_relIndex_eq_two {N T : Subgroup G} (hT : IsCyclic T)
    (h : T.relIndex N = 2) : Group.IsSolvable N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (T.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two h
  have h1 : Group.IsSolvable (T.subgroupOf N) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext (Subtype.ext (mul_comm_of_isCyclic hT (Subgroup.mem_subgroupOf.mp x.2)
      (Subgroup.mem_subgroupOf.mp y.2)))
  have hc : Nat.card (N ⧸ T.subgroupOf N) = 2 := h
  have : IsCyclic (N ⧸ T.subgroupOf N) := isCyclic_of_prime_card hc
  exact Group.isSolvable_of_subgroup_quotient (T.subgroupOf N)

theorem le_of_isPGroup_of_le {N S₀ S₁ : Subgroup G} (hsyl : ¬ 2 ∣ S₀.relIndex N)
    (h01 : S₀ ≤ S₁) (h1N : S₁ ≤ N) (h12 : IsPGroup 2 S₁) : S₁ ≤ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex S₀ S₁ N h01 h1N
  obtain ⟨k, hk⟩ := h12.exists_card_eq
  have hdvd : S₀.relIndex S₁ ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card S₀ S₁
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    apply hsyl
    rw [← hmul, hj]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hj0) _
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

theorem exists_conj_mem_of_isPGroup {N S₀ : Subgroup G} (hS₀N : S₀ ≤ N) (hS₀2 : IsPGroup 2 S₀)
    (hsyl : ¬ 2 ∣ S₀.relIndex N) (hnorm : ∀ x ∈ Subgroup.normalizer (S₀ : Set G), x ∈ N)
    {E : Subgroup G} (hE : IsPGroup 2 E) : ∃ g : G, ∀ e ∈ E, g⁻¹ * e * g ∈ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS₀2.exists_le_sylow
  have hQS : (Q : Subgroup G) ≤ S₀ := by
    have hnil : Group.IsNilpotent (Q : Subgroup G) := Q.isPGroup'.isNilpotent
    have hcond := (normalizerCondition_iff_only_full_group_self_normalizing).mp
      (Group.normalizerCondition_of_isNilpotent (G := (Q : Subgroup G)))
    have hH : Subgroup.normalizer ((S₀.subgroupOf Q : Subgroup (Q : Subgroup G)) :
        Set (Q : Subgroup G)) = S₀.subgroupOf Q := by
      apply le_antisymm _ (Subgroup.le_normalizer)
      intro x hx
      have hx' : (x : G) ∈ Subgroup.normalizer (S₀ : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hs
          have := (Subgroup.mem_normalizer_iff.mp hx ⟨s, hQ hs⟩).mp
            (Subgroup.mem_subgroupOf.mpr hs)
          simpa using Subgroup.mem_subgroupOf.mp this
        · intro hs
          have hsQ : s ∈ (Q : Subgroup G) := by
            have h1 : (x : G) * s * (x : G)⁻¹ ∈ (Q : Subgroup G) := hQ hs
            have h2 : s = (x : G)⁻¹ * ((x : G) * s * (x : G)⁻¹) * (x : G) := by group
            rw [h2]
            exact Q.mul_mem (Q.mul_mem (Q.inv_mem x.2) h1) x.2
          have := (Subgroup.mem_normalizer_iff.mp hx ⟨s, hsQ⟩).mpr
            (Subgroup.mem_subgroupOf.mpr (by simpa using hs))
          exact Subgroup.mem_subgroupOf.mp this
      have hxN := hnorm _ hx'
      have hS₁ : S₀ ⊔ Subgroup.zpowers (x : G) ≤ S₀ := by
        refine le_of_isPGroup_of_le hsyl le_sup_left
          (sup_le hS₀N (Subgroup.zpowers_le.mpr hxN)) ?_
        exact Q.isPGroup'.to_le (sup_le hQ (Subgroup.zpowers_le.mpr x.2))
      exact Subgroup.mem_subgroupOf.mpr
        (hS₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    have htop := hcond _ hH
    intro x hx
    have : (⟨x, hx⟩ : (Q : Subgroup G)) ∈ S₀.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨Q', hQ'⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  refine ⟨g, fun e he => ?_⟩
  have he' : e ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hQ' he
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at he'
  apply hQS
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using he'

theorem exists_conj_mem_of_isPGroup_of_le {W N S₀ E : Subgroup G} (hNW : N ≤ W)
    (hS₀N : S₀ ≤ N) (hS₀2 : IsPGroup 2 S₀) (hsyl : ¬ 2 ∣ S₀.relIndex N)
    (hnorm : ∀ x ∈ W, x ∈ Subgroup.normalizer (S₀ : Set G) → x ∈ N) (hEW : E ≤ W)
    (hE : IsPGroup 2 E) : ∃ g ∈ W, ∀ e ∈ E, g⁻¹ * e * g ∈ S₀ := by
  have hS₀W : S₀ ≤ W := hS₀N.trans hNW
  have hnorm' : ∀ x ∈ Subgroup.normalizer ((S₀.subgroupOf W : Subgroup W) : Set W),
      x ∈ N.subgroupOf W := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    apply hnorm _ x.2
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have := (Subgroup.mem_normalizer_iff.mp hx ⟨s, hS₀W hs⟩).mp (Subgroup.mem_subgroupOf.mpr hs)
      simpa using Subgroup.mem_subgroupOf.mp this
    · intro hs
      have hsW : s ∈ W := by
        have h1 : (x : G) * s * (x : G)⁻¹ ∈ W := hS₀W hs
        have h2 : s = (x : G)⁻¹ * ((x : G) * s * (x : G)⁻¹) * (x : G) := by group
        rw [h2]
        exact W.mul_mem (W.mul_mem (W.inv_mem x.2) h1) x.2
      have := (Subgroup.mem_normalizer_iff.mp hx ⟨s, hsW⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hs))
      exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup (N := N.subgroupOf W) (S₀ := S₀.subgroupOf W)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hS₀N (Subgroup.mem_subgroupOf.mp hx)))
    hS₀2.comap_subtype (by rwa [Subgroup.relIndex_subgroupOf hNW]) hnorm'
    (E := E.subgroupOf W) hE.comap_subtype
  refine ⟨g, g.2, fun e he => ?_⟩
  have := hg ⟨e, hEW he⟩ (Subgroup.mem_subgroupOf.mpr he)
  simpa using Subgroup.mem_subgroupOf.mp this

structure BadCase (W N T : Subgroup G) (z p₀ a : G) (k : ℕ) : Prop where
  le_W : N ≤ W
  le_N : T ≤ N
  isCyclic : IsCyclic T
  relIndex_eq : T.relIndex N = 2
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  centralizer_z : ∀ x ∈ W, x * z = z * x → x ∈ N
  p₀_mem : p₀ ∈ N
  p₀_central : ∀ x ∈ N, x * p₀ = p₀ * x
  pow_eq : (p₀ * p₀) ^ k = z
  orderOf_a : orderOf a = 3
  centralizer_a : ∀ x ∈ W, x * a = a * x → x ∈ T
  inverts_a : ∀ x ∈ W, x * a = a * a * x → x ∈ N

namespace BadCase

variable {W N T : Subgroup G} {z p₀ a : G} {k : ℕ}

omit [Finite G] in
theorem z_mem (h : BadCase W N T z p₀ a k) : z ∈ T := by
  rw [← h.pow_eq]
  exact T.pow_mem (mul_self_mem_of_relIndex_eq_two h.relIndex_eq h.p₀_mem) k

omit [Finite G] in
theorem z_central (h : BadCase W N T z p₀ a k) {x : G} (hx : x ∈ N) : x * z = z * x := by
  rw [← h.pow_eq]
  have hc : Commute x p₀ := h.p₀_central x hx
  exact ((hc.mul_right hc).pow_right k).eq

theorem eq_z (h : BadCase W N T z p₀ a k) {x : G} (hx : x ∈ T) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    x = z :=
  eq_of_sq_eq_one_of_isCyclic h.isCyclic hx h.z_mem hx2 h.z_mul_self hx1 h.z_ne_one

theorem mul_z_comm (h : BadCase W N T z p₀ a k) {u x : G} (huz : u * u = z)
    (hxu : x * u * x⁻¹ ∈ N) : x * z = z * x := by
  have h1 : x * z * x⁻¹ = x * u * x⁻¹ * (x * u * x⁻¹) := by rw [← huz]; group
  have h2 : x * z * x⁻¹ ∈ T := h1 ▸ mul_self_mem_of_relIndex_eq_two h.relIndex_eq hxu
  have h3 : x * z * x⁻¹ * (x * z * x⁻¹) = 1 := by
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have h4 : x * z * x⁻¹ ≠ 1 := by
    intro h5
    apply h.z_ne_one
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h5]; group
  have h5 := h.eq_z h2 h3 h4
  calc x * z = x * z * x⁻¹ * x := by group
    _ = z * x := by rw [h5]

theorem exists_conj (h : BadCase W N T z p₀ a k) {E : Subgroup G} (hEW : E ≤ W)
    (hE : IsPGroup 2 E) : ∃ g ∈ W, ∀ e ∈ E, g⁻¹ * e * g ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huN : p₀ ^ k ∈ N := N.pow_mem h.p₀_mem k
  have huz : p₀ ^ k * p₀ ^ k = z := by rw [← h.pow_eq, (Commute.refl p₀).mul_pow]
  set u : N := ⟨p₀ ^ k, huN⟩ with hu
  have hu4 : u ^ 4 = 1 := Subtype.ext (by
    change (p₀ ^ k) ^ 4 = 1
    calc (p₀ ^ k) ^ 4 = (p₀ ^ k * p₀ ^ k) * (p₀ ^ k * p₀ ^ k) := by group
      _ = 1 := by rw [huz, h.z_mul_self])
  have hU : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have h1 : orderOf x ∣ 2 ^ 2 := by
      have := orderOf_dvd_of_mem_zpowers x.2
      rw [Subgroup.orderOf_coe] at this
      norm_num
      exact this.trans (orderOf_dvd_of_pow_eq_one hu4)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, hj⟩
  obtain ⟨P, hP⟩ := hU.exists_le_sylow
  set S₀ : Subgroup G := (P : Subgroup N).map N.subtype with hS₀
  have hS₀N : S₀ ≤ N := Subgroup.map_subtype_le _
  have hS₀2 : IsPGroup 2 S₀ := P.isPGroup'.map N.subtype
  have hsub : S₀.subgroupOf N = P :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hsyl : ¬ 2 ∣ S₀.relIndex N := by
    rw [Subgroup.relIndex, hsub]
    exact P.not_dvd_index
  have huS₀ : p₀ ^ k ∈ S₀ := ⟨u, hP (Subgroup.mem_zpowers u), rfl⟩
  have hnorm : ∀ x ∈ W, x ∈ Subgroup.normalizer (S₀ : Set G) → x ∈ N := by
    intro x hxW hx
    apply h.centralizer_z x hxW
    exact h.mul_z_comm huz (hS₀N ((Subgroup.mem_normalizer_iff.mp hx _).mp huS₀))
  obtain ⟨g, hgW, hg⟩ := exists_conj_mem_of_isPGroup_of_le h.le_W hS₀N hS₀2 hsyl hnorm hEW hE
  exact ⟨g, hgW, fun e he => hS₀N (hg e he)⟩

omit [Finite G] in
theorem mem_map_conj_iff {E : Subgroup G} {g x : G} :
    x ∈ E.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ E := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using he
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]

theorem card_le_four (h : BadCase W N T z p₀ a k) {E : Subgroup G} (hEW : E ≤ W)
    (hE : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hE2 : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using hE e e.2)⟩
  obtain ⟨g, -, hg⟩ := h.exists_conj hEW hE2
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (fun x y hxy => (MulAut.conj g⁻¹).injective hxy)
  have hE'N : E' ≤ N := fun x hx => by
    have := hg _ (mem_map_conj_iff.mp hx)
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at this
  have hE'2 : ∀ x ∈ E', x * x = 1 := fun x hx => by
    have := hE _ (mem_map_conj_iff.mp hx)
    calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = 1 := by rw [this]; group
  have h1 := card_inf_le_two_of_isCyclic h.isCyclic hE'2
  have h2 : T.relIndex E' ≤ T.relIndex N :=
    Subgroup.relIndex_le_of_le_right hE'N (by rw [h.relIndex_eq]; norm_num)
  rw [h.relIndex_eq] at h2
  have h3 := Subgroup.relIndex_mul_card T E'
  rw [← hcard, ← h3]
  calc T.relIndex E' * Nat.card (T ⊓ E' : Subgroup G) ≤ 2 * 2 := Nat.mul_le_mul h2 h1
    _ = 4 := by norm_num

omit [Finite G] in
theorem a_mem (h : BadCase W N T z p₀ a k) (haW : a ∈ W) : a ∈ T :=
  h.centralizer_a a haW rfl

theorem pCore_eq_bot (h : BadCase W N T z p₀ a k) {Y : Subgroup G} (hYW : Y ≤ W) (haY : a ∈ Y)
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : CFSG.pCore 2 ↥Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    CFSG.AGLEmbedding.TrialityTwo.Seven.isPerfect_of_isLThreeTwo hY
  have htop : ∀ y : ↥Y, ∃ t ∈ (⊤ : Subgroup ↥Y), ∃ p ∈ CFSG.pCore 2 ↥Y, y = t * p :=
    fun y => ⟨y, Subgroup.mem_top y, 1, Subgroup.one_mem _, (mul_one y).symm⟩
  set a' : ↥Y := ⟨a, haY⟩ with ha'
  have ha'3 : orderOf (⟨a', Subgroup.mem_top a'⟩ : (⊤ : Subgroup ↥Y)) = 3 := by
    rw [Subgroup.orderOf_mk, ha', Subgroup.orderOf_mk, h.orderOf_a]
  have hodd : ¬ 2 ∣ orderOf (⟨a', Subgroup.mem_top a'⟩ : (⊤ : Subgroup ↥Y)) := by
    rw [ha'3]; norm_num
  by_contra hQ
  set E := CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 ↥Y) with hEdef
  have hE1 : E ≠ ⊥ := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hQ2 hQ
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    rw [← pow_two]
    exact (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (CFSG.pCore 2 ↥Y)).2 e he
  have hEn : E.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    calc (⊤ : Subgroup ↥Y) = Subgroup.normalizer ((CFSG.pCore 2 ↥Y : Subgroup ↥Y) : Set ↥Y) :=
          (Subgroup.normalizer_eq_top (CFSG.pCore 2 ↥Y)).symm
      _ ≤ _ := CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _
  have hEcard : Nat.card E ≤ 4 := by
    have hmap : Nat.card (E.map Y.subtype) = Nat.card E :=
      Subgroup.card_map_of_injective Y.subtype_injective
    rw [← hmap]
    refine h.card_le_four ((Subgroup.map_subtype_le E).trans hYW) ?_
    rintro _ ⟨e, he, rfl⟩
    have := hEsq e he
    simpa using congrArg Subtype.val this
  have hsolv : Group.IsSolvable (Equiv.Perm ↥E) := Equiv.Perm.isSolvable hEcard
  let ψ : (⊤ : Subgroup ↥Y) →* Equiv.Perm ↥E :=
    (MulAut.toPerm ↥E).comp ((MulAut.conjNormal (H := E)).comp (⊤ : Subgroup ↥Y).subtype)
  have hψ := map_eq_one_of_solvable (CFSG.pCore 2 ↥Y) hQ2 hperf ⊤ htop ψ _ hodd
  have hcomm : ∀ e ∈ E, a' * e = e * a' := by
    intro e he
    have h1 : MulAut.conjNormal a' (⟨e, he⟩ : ↥E) = ⟨e, he⟩ := DFunLike.congr_fun hψ ⟨e, he⟩
    have h2 : a' * e * a'⁻¹ = e := by
      have := congrArg Subtype.val h1
      rwa [MulAut.conjNormal_apply] at this
    calc a' * e = a' * e * a'⁻¹ * a' := by group
      _ = e * a' := by rw [h2]
  have hEz : ∀ e ∈ E, e ≠ 1 → (e : G) = z := by
    intro e he he1
    have heT : (e : G) ∈ T := h.centralizer_a _ (hYW e.2)
      (by have := congrArg Subtype.val (hcomm e he); simpa using this.symm)
    refine h.eq_z heT (by simpa using congrArg Subtype.val (hEsq e he)) ?_
    intro h1
    exact he1 (Subtype.ext h1)
  obtain ⟨e₀, he₀, he₀1⟩ := (Subgroup.nontrivial_iff_exists_ne_one E).mp
    ((Subgroup.nontrivial_iff_ne_bot E).mpr hE1)
  have hze₀ := hEz e₀ he₀ he₀1
  have hYN : Y ≤ N := by
    intro y hy
    apply h.centralizer_z y (hYW hy)
    set y' : ↥Y := ⟨y, hy⟩
    have hmem : y' * e₀ * y'⁻¹ ∈ E := hEn.conj_mem e₀ he₀ y'
    have hne : y' * e₀ * y'⁻¹ ≠ 1 := by
      intro h1
      apply he₀1
      calc e₀ = y'⁻¹ * (y' * e₀ * y'⁻¹) * y' := by group
        _ = 1 := by rw [h1]; group
    have h2 := hEz _ hmem hne
    rw [← hze₀]
    have h3 : (y : G) * (e₀ : G) * (y : G)⁻¹ = e₀ := by
      rw [← hze₀] at h2
      simpa using h2
    calc (y : G) * (e₀ : G) = (y : G) * (e₀ : G) * (y : G)⁻¹ * y := by group
      _ = e₀ * y := by rw [h3]
  have hNsolv : Group.IsSolvable N := isSolvable_of_relIndex_eq_two h.isCyclic h.relIndex_eq
  have h1 := map_eq_one_of_solvable (CFSG.pCore 2 ↥Y) hQ2 hperf ⊤ htop
    ((Subgroup.inclusion hYN).comp (⊤ : Subgroup ↥Y).subtype) _ hodd
  have h2 : a = 1 := congrArg Subtype.val h1
  have := h.orderOf_a
  rw [h2, orderOf_one] at this
  norm_num at this

theorem false_of_isLThreeTwo (h : BadCase W N T z p₀ a k) {Y : Subgroup G} (hYW : Y ≤ W)
    (haY : a ∈ Y) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := h.pCore_eq_bot hYW haY hY
  have hYL : IsLThreeTwo ↥Y := by
    obtain ⟨d, hd, ⟨e⟩⟩ := hY
    exact ⟨d, hd, ⟨(QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hQ.symm)).trans e⟩⟩
  have haT : a ∈ T := h.a_mem (hYW haY)
  set a' : ↥Y := ⟨a, haY⟩ with ha'
  have ha'3 : orderOf a' = 3 := by rw [ha', Subgroup.orderOf_mk, h.orderOf_a]
  obtain ⟨y', hy'2, hy'a⟩ := exists_inverting_involution_of_isLThreeTwo hYL ha'3
  have hyW : (y' : G) ∈ W := hYW y'.2
  have hya : (y' : G) * a = a * a * y' := congrArg Subtype.val hy'a
  have hyN : (y' : G) ∈ N := h.inverts_a _ hyW hya
  set C := Subgroup.centralizer ({y'} : Set ↥Y) with hC
  have hCcard : Nat.card C = 8 := card_centralizer_of_isLThreeTwo hYL hy'2
  set D := C.map Y.subtype with hD
  have hDcard : Nat.card D = 8 := by
    rw [hD, Subgroup.card_map_of_injective Y.subtype_injective, hCcard]
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hDcard]; norm_num)
  obtain ⟨g, hgW, hg⟩ := h.exists_conj ((Subgroup.map_subtype_le C).trans hYW) hD2
  set D' := D.map (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hD'card : Nat.card D' = 8 := by
    rw [hD', Subgroup.card_map_of_injective (fun x y hxy => (MulAut.conj g⁻¹).injective hxy),
      hDcard]
  have hD'N : D' ≤ N := fun x hx => by
    have := hg _ (mem_map_conj_iff.mp hx)
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at this
  have h2 : T.relIndex D' ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := T) hD'N (by rw [h.relIndex_eq]; norm_num)
    rwa [h.relIndex_eq] at this
  have h3 := Subgroup.relIndex_mul_card T D'
  rw [hD'card] at h3
  have hdvd : 2 ∣ Nat.card (T ⊓ D' : Subgroup G) := by
    have hpos : 0 < T.relIndex D' := Nat.pos_of_ne_zero (by intro h0; rw [h0] at h3; omega)
    rcases (by omega : T.relIndex D' = 1 ∨ T.relIndex D' = 2) with hr | hr <;>
      rw [hr] at h3 <;> omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxz : (x : G) = z := by
    have hx2 : (x : G) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      simpa using congrArg Subtype.val this
    have hx1 : (x : G) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      norm_num at hx
    exact h.eq_z x.2.1 hx2 hx1
  have hzD' : z ∈ D' := hxz ▸ x.2.2
  obtain ⟨c, hcC, hcz⟩ := Subgroup.mem_map.mp (mem_map_conj_iff.mp hzD')
  have hcc : ∀ d ∈ C, c * d = d * c := by
    intro d hd
    have hdN : g⁻¹ * d * g ∈ N := hg _ ⟨d, hd, rfl⟩
    have hcomm := h.z_central hdN
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (c : G) = g * z * g⁻¹ from hcz]
    calc g * z * g⁻¹ * d = g * (z * (g⁻¹ * d * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * d * g) * z) * g⁻¹ := by rw [hcomm]
      _ = d * (g * z * g⁻¹) := by group
  have hc1 : c ≠ 1 := by
    intro h1
    apply h.z_ne_one
    have : g * z * g⁻¹ = 1 := by rw [← hcz, h1, map_one]
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have hcy : c = y' := by
    rcases eq_one_or_eq_of_mem_center_centralizer hYL hy'2 hcC hcc with h1 | h1
    · exact absurd h1 hc1
    · exact h1
  have hyg : (y' : G) = g * z * g⁻¹ := by rw [← hcy]; exact hcz
  have hp₀y : (y' : G) * p₀ = p₀ * y' := h.p₀_central _ hyN
  have hp₁W : g⁻¹ * p₀ * g ∈ W :=
    W.mul_mem (W.mul_mem (W.inv_mem hgW) (h.le_W h.p₀_mem)) hgW
  have hp₁N : g⁻¹ * p₀ * g ∈ N := by
    apply h.centralizer_z _ hp₁W
    have hz : z = g⁻¹ * y' * g := by rw [hyg]; group
    rw [hz]
    calc g⁻¹ * p₀ * g * (g⁻¹ * y' * g) = g⁻¹ * (p₀ * y') * g := by group
      _ = g⁻¹ * (y' * p₀) * g := by rw [hp₀y]
      _ = g⁻¹ * y' * g * (g⁻¹ * p₀ * g) := by group
  have hzT : g⁻¹ * z * g ∈ T := by
    have h1 : g⁻¹ * z * g = ((g⁻¹ * p₀ * g) * (g⁻¹ * p₀ * g)) ^ k := by
      rw [← h.pow_eq]
      have e : (g⁻¹ * p₀ * g) * (g⁻¹ * p₀ * g) = g⁻¹ * (p₀ * p₀) * g⁻¹⁻¹ := by group
      rw [e, conj_pow, inv_inv]
    rw [h1]
    exact T.pow_mem (mul_self_mem_of_relIndex_eq_two h.relIndex_eq hp₁N) k
  have hzz : g⁻¹ * z * g = z := by
    refine h.eq_z hzT ?_ ?_
    · calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [h.z_mul_self]; group
    · intro h1
      apply h.z_ne_one
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
  have hyz : (y' : G) = z := by
    rw [hyg]
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hzz]
      _ = z := by group
  have hza : z * a = a * z := mul_comm_of_isCyclic h.isCyclic h.z_mem haT
  rw [hyz, hza] at hya
  have ha1 : a = 1 := mul_eq_left.mp (mul_right_cancel hya).symm
  have := h.orderOf_a
  rw [ha1, orderOf_one] at this
  norm_num at this

end BadCase

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
