module

public import CFSG.LieType.CurtisTits.Amalgam

public section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u v w

variable {K : Type u} [Group K] {ι : Type v} [PartialOrder ι]
variable {L : ι → Subgroup K}

theorem IsUniversalCompletion.congr_orderIso {ι' : Type v} [PartialOrder ι']
    {L' : ι' → Subgroup K} (e : ι ≃o ι') (hL' : ∀ i, L' (e i) = L i)
    (hU : IsUniversalCompletion.{u, v, w} L) : IsUniversalCompletion.{u, v, w} L' := by
  intro Y _ φ hφ
  let incl : ∀ i, L i →* L' (e i) :=
    fun i => (MulEquiv.subgroupCongr (hL' i)).symm.toMonoidHom
  have incl_coe : ∀ (i : ι) (x : L i), ((incl i x : L' (e i)) : K) = (x : K) :=
    fun i x => MulEquiv.subgroupCongr_symm_apply (hL' i) x
  let φe : ∀ i, L i →* Y := fun i => (φ (e i)).comp (incl i)
  have hφe : IsCompatible L φe := by
    intro i j hij x y hxy
    exact hφ (e i) (e j) (e.monotone hij) (incl i x) (incl j y) (by
      rw [incl_coe, incl_coe]
      exact hxy)
  obtain ⟨Ψ, hΨ, hΨuniq⟩ := hU Y φe hφe
  refine ⟨Ψ, ?_, ?_⟩
  · intro i' x
    have key : ∀ (i : ι) (x : L' (e i)), Ψ x = φ (e i) x := by
      intro i x
      have h1 := hΨ i ((MulEquiv.subgroupCongr (hL' i)) x)
      have h2 : ((MulEquiv.subgroupCongr (hL' i)) x : K) = (x : K) :=
        MulEquiv.subgroupCongr_apply (hL' i) x
      rw [h2] at h1
      have hy : incl i ((MulEquiv.subgroupCongr (hL' i)) x) = x := by
        apply Subtype.ext
        rw [incl_coe, MulEquiv.subgroupCongr_apply]
      simpa [φe, hy] using h1
    obtain ⟨i, rfl⟩ : ∃ i, e i = i' := ⟨e.symm i', e.apply_symm_apply i'⟩
    exact key i x
  · intro Ψ' hΨ'
    apply hΨuniq Ψ'
    intro i x
    have h1 : Ψ' (incl i x) = φ (e i) (incl i x) := hΨ' (e i) (incl i x)
    have h2 : (incl i x : K) = (x : K) := incl_coe i x
    have h3 : Ψ' (incl i x) = Ψ' x := by rw [h2]
    show Ψ' x = φe i x
    rw [← h3]
    exact h1

@[expose] def ExtendsUniquely (L : ι → Subgroup K) (S : Set ι) : Prop :=
  ∀ (G : Type w) [Group G] (φ : ∀ i : S, L i.1 →* G),
    IsCompatible (fun i : S => L i.1) φ →
    ∃! ψ : ∀ i : ι, L i →* G,
      IsCompatible L ψ ∧ ∀ i : S, ψ i.1 = φ i

theorem extendsUniquely_univ (L : ι → Subgroup K) : ExtendsUniquely.{u, v, w} L Set.univ := by
  intro Y _ φ hφ
  let ψ : ∀ i : ι, L i →* Y := fun i => φ ⟨i, Set.mem_univ i⟩
  have hψ : IsCompatible L ψ := by
    intro i j hij x y hxy
    exact hφ ⟨i, Set.mem_univ i⟩ ⟨j, Set.mem_univ j⟩ hij x y hxy
  refine ⟨ψ, ⟨hψ, ?_⟩, ?_⟩
  · intro i
    have hi : i = ⟨i.1, Set.mem_univ i.1⟩ := Subtype.ext rfl
    rw [hi]
  · intro ψ' hψ'
    funext i
    simpa [ψ] using hψ'.2 ⟨i, Set.mem_univ i⟩

theorem existsUnique_isCompatible_insert (hL : Monotone L) {S : Set ι} {j : ι}
    (hS : IsLowerSet S) (hj : j ∉ S) (hSj : ∀ i, i < j → i ∈ S)
    (hloc : IsUniversalCompletion.{u, v, w}
      (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j)))
    {Y : Type w} [Group Y] (φ : ∀ i : S, L i.1 →* Y)
    (hφ : IsCompatible (fun i : S => L i.1) φ) :
    ∃! φ' : ∀ i : ↥(insert j S), L i.1 →* Y,
      IsCompatible (fun i : ↥(insert j S) => L i.1) φ' ∧
        ∀ i : S, φ' ⟨i.1, Set.mem_insert_of_mem j i.2⟩ = φ i := by
  classical
  let θ : ∀ i : {i : ι // i < j}, (L i.1).subgroupOf (L j) →* Y :=
    fun i => (φ ⟨i.1, hSj i.1 i.2⟩).comp
      (Subgroup.subgroupOfEquivOfLe (hL i.2.le)).toMonoidHom
  have hθ : IsCompatible (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j)) θ := by
    intro i i' hii' x y hxy
    refine hφ ⟨i.1, hSj i.1 i.2⟩ ⟨i'.1, hSj i'.1 i'.2⟩ hii'
      (Subgroup.subgroupOfEquivOfLe (hL i.2.le) x)
      (Subgroup.subgroupOfEquivOfLe (hL i'.2.le) y) ?_
    rw [Subgroup.subgroupOfEquivOfLe_apply_coe, Subgroup.subgroupOfEquivOfLe_apply_coe]
    exact congrArg (fun z : L j => (z : K)) hxy
  obtain ⟨ψj, hψj, hψjuniq⟩ := hloc Y θ hθ
  let φ' : ∀ k : ↥(insert j S), L k.1 →* Y := fun k =>
    if h : k.1 = j then ψj.comp (MulEquiv.subgroupCongr (congrArg L h)).toMonoidHom
    else φ ⟨k.1, by
      rcases Set.mem_insert_iff.1 k.2 with hk | hk
      · exact absurd hk h
      · exact hk⟩
  have phiJ : ∀ (hp : j ∈ insert j S), φ' ⟨j, hp⟩ = ψj := by
    intro hp
    simp only [φ', dif_pos rfl]
    rw [show (MulEquiv.subgroupCongr (congrArg L rfl)).toMonoidHom = MonoidHom.id (L j) from rfl]
    exact MonoidHom.comp_id ψj
  have phiS : ∀ i : S, φ' ⟨i.1, Set.mem_insert_of_mem j i.2⟩ = φ i := by
    intro i
    have hne : i.1 ≠ j := fun h => hj (h ▸ i.2)
    simp only [φ', dif_neg hne]
  have hφ' : IsCompatible (fun i : ↥(insert j S) => L i.1) φ' := by
    rintro ⟨kv, kp⟩ ⟨kv', kp'⟩ hkk' x y hxy
    by_cases hk : kv = j
    · subst kv
      by_cases hk' : kv' = j
      · subst kv'
        have hx : φ' ⟨j, kp⟩ x = ψj x := DFunLike.congr_fun (phiJ kp) x
        have hy : φ' ⟨j, kp'⟩ y = ψj y := DFunLike.congr_fun (phiJ kp') y
        rw [hx, hy]
        exact congrArg ψj (Subtype.ext hxy)
      · exfalso
        have hk'S : kv' ∈ S := by
          rcases Set.mem_insert_iff.1 kp' with h | h
          · exact absurd h hk'
          · exact h
        exact hj (hS (show j ≤ kv' from hkk') hk'S)
    · by_cases hk' : kv' = j
      · subst kv'
        have hkS : kv ∈ S := by
          rcases Set.mem_insert_iff.1 kp with h | h
          · exact absurd h hk
          · exact h
        have hlt : kv < j := lt_of_le_of_ne (show kv ≤ j from hkk') hk
        have hy : (y : K) ∈ L kv := by
          rw [← hxy]
          exact x.2
        have hx := hψj ⟨kv, hlt⟩ (⟨y, hy⟩ : (L kv).subgroupOf (L j))
        have hψ : ψj y = θ ⟨kv, hlt⟩ (⟨y, hy⟩ : (L kv).subgroupOf (L j)) := by
          simpa using hx
        have hx' : φ' ⟨kv, kp⟩ x = φ ⟨kv, hkS⟩ x := by
          simp only [φ', dif_neg hk]
        have hy' : φ' ⟨j, kp'⟩ y = ψj y := DFunLike.congr_fun (phiJ kp') y
        rw [hx', hy', hψ]
        have hφk : φ ⟨kv, hkS⟩ = φ ⟨kv, hSj kv hlt⟩ := by
          have hproof : (⟨kv, hkS⟩ : S) = ⟨kv, hSj kv hlt⟩ := Subtype.ext rfl
          cases hproof
          rfl
        rw [hφk]
        show φ ⟨kv, hSj kv hlt⟩ x =
          φ ⟨kv, hSj kv hlt⟩ (Subgroup.subgroupOfEquivOfLe (hL hlt.le)
            (⟨y, hy⟩ : (L kv).subgroupOf (L j)))
        exact congrArg _ (Subtype.ext (by
          rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
          exact hxy))
      · have hkS : kv ∈ S := by
          rcases Set.mem_insert_iff.1 kp with h | h
          · exact absurd h hk
          · exact h
        have hk'S : kv' ∈ S := by
          rcases Set.mem_insert_iff.1 kp' with h | h
          · exact absurd h hk'
          · exact h
        have hx' : φ' ⟨kv, kp⟩ x = φ ⟨kv, hkS⟩ x := by
          simp only [φ', dif_neg hk]
        have hy' : φ' ⟨kv', kp'⟩ y = φ ⟨kv', hk'S⟩ y := by
          simp only [φ', dif_neg hk']
        rw [hx', hy']
        exact hφ ⟨kv, hkS⟩ ⟨kv', hk'S⟩ (show kv ≤ kv' from hkk') x y hxy
  refine ⟨φ', ⟨hφ', phiS⟩, ?_⟩
  intro φ'' hφ''
  funext k
  rcases k with ⟨kv, kp⟩
  by_cases hk : kv = j
  · subst kv
    rw [phiJ kp]
    apply hψjuniq
    intro i x
    let kS : ↥(insert j S) := ⟨i.1, Set.mem_insert_of_mem j (hSj i.1 i.2)⟩
    have h := hφ''.1 kS ⟨j, kp⟩ (show kS ≤ ⟨j, kp⟩ from i.2.le)
      (Subgroup.subgroupOfEquivOfLe (hL i.2.le) x) x (by
        rw [Subgroup.subgroupOfEquivOfLe_apply_coe])
    have hext := hφ''.2 ⟨i.1, hSj i.1 i.2⟩
    calc φ'' ⟨j, kp⟩ x = φ'' kS (Subgroup.subgroupOfEquivOfLe (hL i.2.le) x) := h.symm
      _ = φ ⟨i.1, hSj i.1 i.2⟩ (Subgroup.subgroupOfEquivOfLe (hL i.2.le) x) := by
          rw [hext]
      _ = θ i x := rfl
  · have hkS : kv ∈ S := by
      rcases Set.mem_insert_iff.1 kp with h | h
      · exact absurd h hk
      · exact h
    rw [show (⟨kv, kp⟩ : ↥(insert j S)) = ⟨kv, Set.mem_insert_of_mem j hkS⟩ from
      Subtype.ext rfl, phiS ⟨kv, hkS⟩]
    exact hφ''.2 ⟨kv, hkS⟩

theorem extendsUniquely_insert (hL : Monotone L) {S : Set ι} {j : ι} (hS : IsLowerSet S)
    (hj : j ∉ S) (hSj : ∀ i, i < j → i ∈ S)
    (hloc : IsUniversalCompletion.{u, v, w}
      (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j)))
    (hU : ExtendsUniquely.{u, v, w} L (insert j S)) : ExtendsUniquely.{u, v, w} L S := by
  intro Y _ φ hφ
  obtain ⟨φ', ⟨hφ'compat, hφ'ext⟩, hφ'uniq⟩ :=
    existsUnique_isCompatible_insert hL hS hj hSj hloc φ hφ
  obtain ⟨Ψ, hΨ, hΨuniq⟩ := hU Y φ' hφ'compat
  refine ⟨Ψ, ⟨hΨ.1, ?_⟩, ?_⟩
  · intro i
    exact (hΨ.2 ⟨i.1, Set.mem_insert_of_mem j i.2⟩).trans (hφ'ext i)
  · rintro Ψ' ⟨hΨ'compat, hΨ'ext⟩
    have hΨ'S : (fun k : ↥(insert j S) => Ψ' k.1) = φ' := by
      apply hφ'uniq
      exact ⟨fun k k' hkk' x y hxy => hΨ'compat k.1 k'.1 hkk' x y hxy,
        fun i => hΨ'ext i⟩
    apply hΨuniq Ψ'
    exact ⟨hΨ'compat, fun k => congrArg (fun f => f k) hΨ'S⟩

theorem extendsUniquely_of_isLowerSet [Finite ι] (hL : Monotone L) :
    ∀ {S : Set ι}, IsLowerSet S →
      (∀ j ∉ S,
        IsUniversalCompletion.{u, v, w}
          (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j))) →
      ExtendsUniquely.{u, v, w} L S := by
  intro S hS hloc
  suffices H : ∀ n, ∀ (S : Set ι), IsLowerSet S →
      (∀ j ∉ S,
        IsUniversalCompletion.{u, v, w}
          (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j))) →
      (Sᶜ).ncard = n → ExtendsUniquely.{u, v, w} L S from
    H _ S hS hloc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hloc hn
    by_cases hne : Sᶜ = ∅
    · have hS_univ : S = Set.univ := Set.compl_empty_iff.1 hne
      rw [hS_univ]
      exact extendsUniquely_univ L
    · have hne' : (Sᶜ).Nonempty := Set.nonempty_iff_ne_empty.2 hne
      obtain ⟨j, hjC, hjmin⟩ := (Set.toFinite (Sᶜ)).exists_minimal hne'
      have hj : j ∉ S := hjC
      have hSj : ∀ i, i < j → i ∈ S := by
        intro i hij
        by_contra hi
        exact (not_le_of_gt hij) (hjmin hi hij.le)
      have hS' : IsLowerSet (insert j S) := by
        intro a b hab hb
        rcases Set.mem_insert_iff.1 hb with haj | haS
        · rw [haj] at hab
          rcases eq_or_lt_of_le hab with hbj | hlt
          · rw [hbj]
            exact by simp
          · exact Set.mem_insert_of_mem j (hSj b hlt)
        · exact Set.mem_insert_of_mem j (hS hab haS)
      have hsub : (insert j S)ᶜ ⊂ Sᶜ := by
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Set.mem_compl_iff] at hx ⊢
          intro hxS
          exact hx (Set.mem_insert_of_mem j hxS)
        · intro hcontra
          have hmem : j ∈ (insert j S)ᶜ := hcontra hjC
          rw [Set.mem_compl_iff] at hmem
          exact hmem (by simp)
      have hlt : ((insert j S)ᶜ).ncard < n := by
        have h := Set.ncard_lt_ncard hsub (Set.toFinite (Sᶜ))
        rwa [hn] at h
      have hloc' : ∀ k ∉ insert j S,
          IsUniversalCompletion.{u, v, w}
            (fun i : {i : ι // i < k} => (L i.1).subgroupOf (L k)) := by
        intro k hk
        exact hloc k (fun hkS => hk (Set.mem_insert_of_mem j hkS))
      exact extendsUniquely_insert hL hS hj hSj (hloc j hj)
        (ih _ hlt (insert j S) hS' hloc' rfl)

theorem isUniversalCompletion_restrict [Finite ι] (hL : Monotone L) {S : Set ι}
    (hS : IsLowerSet S)
    (hloc : ∀ j ∉ S,
      IsUniversalCompletion.{u, v, w}
        (fun i : {i : ι // i < j} => (L i.1).subgroupOf (L j)))
    (hU : IsUniversalCompletion.{u, v, w} L) :
    IsUniversalCompletion.{u, v, w} (fun i : S => L i.1) := by
  intro Y _ φ hφ
  obtain ⟨ψ, hψ, hψuniq⟩ := extendsUniquely_of_isLowerSet hL hS hloc Y φ hφ
  obtain ⟨Ψ, hΨ, hΨuniq⟩ := hU Y ψ hψ.1
  refine ⟨Ψ, ?_, ?_⟩
  · intro i x
    exact (hΨ i.1 x).trans (DFunLike.congr_fun (hψ.2 i) x)
  · intro Ψ' hΨ'
    apply hΨuniq Ψ'
    let ψ' : ∀ i : ι, L i →* Y := fun i => Ψ'.comp (L i).subtype
    have hψ' : IsCompatible L ψ' := by
      intro i j hij x y hxy
      change Ψ' (x : K) = Ψ' (y : K)
      rw [hxy]
    have hψ'ext : ∀ i : S, ψ' i.1 = φ i := by
      intro i
      ext x
      exact hΨ' i x
    have hEq : ψ' = ψ := hψuniq ψ' ⟨hψ', hψ'ext⟩
    intro i x
    have h := congrFun (congrArg (fun f => f i) hEq) x
    simpa [ψ'] using h

end CFSG.LieType.CurtisTits
