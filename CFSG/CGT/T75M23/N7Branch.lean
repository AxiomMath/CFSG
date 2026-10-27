module

public import CFSG.CGT.T75JM.N6Branch
public import CFSG.Assembly.Defs
public import CFSG.CGT.T75M23.N7Class

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM Equiv

structure A7Rel {H : Type*} [Group H] (g h : H) : Prop where
  x2 : g * g = 1
  y5 : h * h * h * h * h = 1
  r3 : (g * h * g * h⁻¹) ^ 3 = 1
  r4 : (h⁻¹ * g) ^ 7 = 1
  r5 : g * h * g * (h * g * h⁻¹ * g * h) ^ 2 * h * g * h⁻¹ = 1

theorem A7Rel.map {H K : Type*} [Group H] [Group K] (f : H →* K) {g h : H} (hr : A7Rel g h) :
    A7Rel (f g) (f h) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [← map_mul] using congrArg f hr.x2
  · simpa [← map_mul] using congrArg f hr.y5
  · simpa [← map_mul, ← map_pow, ← map_inv] using congrArg f hr.r3
  · simpa [← map_mul, ← map_pow, ← map_inv] using congrArg f hr.r4
  · simpa [← map_mul, ← map_pow, ← map_inv] using congrArg f hr.r5

theorem a7Rel : A7Rel (⟨a7x, a7x_mem⟩ : alternatingGroup (Fin 7)) ⟨a7y, a7y_mem⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := a7_rel
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa using h1
  · simpa [pow_succ, mul_assoc] using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5

theorem a7twistRel : A7Rel (⟨a7x, a7x_mem⟩ : alternatingGroup (Fin 7)) ⟨a7twist, a7twist_mem⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := a7twist_rel
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · simpa using h1
  · simpa [pow_succ, mul_assoc] using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5

theorem a7_closure_twist (hn : A7Nodup) :
    Subgroup.closure ({a7x, a7twist} : Set (Perm (Fin 7))) = alternatingGroup (Fin 7) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact a7x_mem
    · exact a7twist_mem
  · rw [← a7_closure hn, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · rw [a7y_eq]
      exact evalG_mem_closure _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) _

variable {G : Type*} [Group G] {T : Subgroup G}

theorem colsOf_evalG (c : Coords T) (g h : Subgroup.normalizer (T : Set G)) (w : List ℕ) :
    colsOf c (evalG g h w) = evalC (colsOf c g) (colsOf c h) w := by
  induction w with
  | nil => simpa [evalG, evalC] using colsOf_one c
  | cons l w ih =>
    simp only [evalG, evalC, colsOf_mul, ih]
    by_cases hl : l = 0 <;> simp [hl]

theorem colsOf_lt' (c : Coords T) (g : Subgroup.normalizer (T : Set G)) (i : Fin 4) :
    (colsOf c g).col i < 16 := by
  fin_cases i <;> exact c.lt _

theorem branch_data7 (c : Coords T) (hC : Subgroup.centralizer (T : Set G) = T)
    (φ : NQ T ≃* alternatingGroup (Fin 7))
    (D : Subgroup (Subgroup.normalizer (T : Set G)))
    (hD1 : T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊓ D = ⊥)
    (hD2 : T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊔ D = ⊤)
    (hmod : ModClass7) (hnodup : A7Nodup) :
    ∃ g h : Subgroup.normalizer (T : Set G), A7Rel g h ∧
      Subgroup.closure ({g, h} : Set (Subgroup.normalizer (T : Set G))) = D ∧
      EquivC7 (colsOf c g) (colsOf c h) := by
  classical
  set Tn : Subgroup ↥(Subgroup.normalizer (T : Set G)) :=
    T.subgroupOf (Subgroup.normalizer (T : Set G)) with hTn
  let π : ↥(Subgroup.normalizer (T : Set G)) →* alternatingGroup (Fin 7) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' Tn)
  have hπsurj : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective Tn)
  have hπker : π.ker = Tn := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ Tn
    rw [map_eq_one_iff _ φ.injective, QuotientGroup.eq_one_iff]
  let πD : D →* alternatingGroup (Fin 7) := π.comp D.subtype
  have hinj : Function.Injective πD := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hd
    have h1 : (d : ↥(Subgroup.normalizer (T : Set G))) ∈ Tn := by rw [← hπker]; exact hd
    have h2 : (d : ↥(Subgroup.normalizer (T : Set G))) ∈ Tn ⊓ D := ⟨h1, d.2⟩
    rw [hD1] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  have hsurj : Function.Surjective πD := by
    intro a
    obtain ⟨n, hn⟩ := hπsurj a
    have hn' : n ∈ Tn ⊔ D := by rw [hD2]; exact Subgroup.mem_top n
    obtain ⟨t, ht, d, hd, hmul⟩ := Subgroup.mem_sup_of_normal_left.1 hn'
    refine ⟨⟨d, hd⟩, ?_⟩
    show π d = a
    rw [← hn, ← hmul, map_mul]
    have : π t = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact ht
    rw [this, one_mul]
  let e : D ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective πD ⟨hinj, hsurj⟩
  let ψ : alternatingGroup (Fin 7) →* ↥(Subgroup.normalizer (T : Set G)) :=
    D.subtype.comp e.symm.toMonoidHom
  have hψπ : ∀ a, π (ψ a) = a := by
    intro a
    have := e.apply_symm_apply a
    exact this
  have hψinj : Function.Injective ψ := fun a b hab => by
    have := congrArg π hab
    rwa [hψπ, hψπ] at this
  have hψrange : ψ.range = D := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [ψ]⟩
  set qa : alternatingGroup (Fin 7) := ⟨a7x, a7x_mem⟩ with hqa
  set qb : alternatingGroup (Fin 7) := ⟨a7y, a7y_mem⟩ with hqb
  set qt : alternatingGroup (Fin 7) := ⟨a7twist, a7twist_mem⟩ with hqt
  have hqt' : qt = evalG qa qb twistWord7 := by
    apply Subtype.ext
    rw [evalG_coe]
    rfl
  set x : ↥(Subgroup.normalizer (T : Set G)) := ψ qa with hx
  set y : ↥(Subgroup.normalizer (T : Set G)) := ψ qb with hy
  have hrel1 : A7Rel x y := a7Rel.map ψ
  have hclos1 : Subgroup.closure ({x, y} : Set ↥(Subgroup.normalizer (T : Set G))) = D := by
    have h1 : Subgroup.closure ({qa, qb} : Set (alternatingGroup (Fin 7))) = ⊤ :=
      closure_pair_eq_top' (a7_closure hnodup).symm a7x_mem a7y_mem
    have := MonoidHom.map_closure ψ ({qa, qb} : Set (alternatingGroup (Fin 7)))
    rw [h1, ← MonoidHom.range_eq_map, hψrange, Set.image_pair] at this
    exact this.symm
  have hinv : y⁻¹ = y ^ 4 := by
    have h5 : y ^ 4 * y = 1 := by
      have := hrel1.y5
      simpa [pow_succ, mul_assoc] using this
    exact inv_eq_of_mul_eq_one_left h5
  have hrel : RelC7 (colsOf c x) (colsOf c y) := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrel1
    have h2' : y ^ 5 = 1 := by simpa [pow_succ, mul_assoc] using h2
    rw [hinv] at h3 h4 h5
    simp only [mul_assoc] at h3 h4 h5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← colsOf_mul, h1, colsOf_one]
    · intro hX
      have hxT : ((x : ↥(Subgroup.normalizer (T : Set G))) : G) ∈
          Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact (commute_of_colsOf c x hX ⟨t, ht⟩).symm
      rw [hC] at hxT
      have : (x : ↥(Subgroup.normalizer (T : Set G))) ∈ Tn := hxT
      have h1 : π x = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact this
      have h2 : π x = qa := hψπ qa
      rw [h2] at h1
      exact a7x_ne_one (congrArg Subtype.val h1)
    · rw [← colsOf_pow, h2', colsOf_one]
    · have := congrArg (colsOf c) h3
      simpa only [colsOf_pow, colsOf_mul, colsOf_one] using this
    · have := congrArg (colsOf c) h4
      simpa only [colsOf_pow, colsOf_mul, colsOf_one] using this
    · have := congrArg (colsOf c) h5
      simpa only [colsOf_pow, colsOf_mul, colsOf_one] using this
  rcases hmod _ _ (colsOf_lt' c x) (colsOf_lt' c y) hrel with hA | hB
  · exact ⟨x, y, hrel1, hclos1, hA⟩
  ·
    set z : ↥(Subgroup.normalizer (T : Set G)) := ψ qt with hz
    have hz' : z = evalG x y twistWord7 := by
      rw [hz, hqt', ← evalG_map ψ]
    have hrel2 : A7Rel x z := a7twistRel.map ψ
    have hclos2 : Subgroup.closure ({x, z} : Set ↥(Subgroup.normalizer (T : Set G))) = D := by
      have h1 : Subgroup.closure ({qa, qt} : Set (alternatingGroup (Fin 7))) = ⊤ := by
        have := closure_pair_eq_top' (a7_closure_twist hnodup).symm a7x_mem a7twist_mem
        exact this
      have := MonoidHom.map_closure ψ ({qa, qt} : Set (alternatingGroup (Fin 7)))
      rw [h1, ← MonoidHom.range_eq_map, hψrange, Set.image_pair] at this
      exact this.symm
    refine ⟨x, z, hrel2, hclos2, ?_⟩
    rw [hz', colsOf_evalG]
    exact hB

end CFSG.CGT.T75M23
