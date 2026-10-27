module

public import CFSG.Certificates.Kernel.Enum.ZCGlue

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem mem_normalizer_conj_closure {A : Type} [Group A] [Finite A] {z u g : A} {p : Nat}
    (hg : ∀ e < p, g * (z ^ e * u * (z ^ e)⁻¹) * g⁻¹ ∈
      Subgroup.closure {c | c ∈ (List.range p).map (fun e => z ^ e * u * (z ^ e)⁻¹)}) :
    g ∈ Subgroup.normalizer
      (Subgroup.closure {c | c ∈ (List.range p).map (fun e => z ^ e * u * (z ^ e)⁻¹)} : Set A) := by
  refine zc_mem_normalizer_of_conj_mem _ fun v hv => ?_
  induction hv using Subgroup.closure_induction with
  | mem c hc =>
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_range] at hc
    obtain ⟨e, he, rfl⟩ := hc
    exact hg e he
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem zcw_of_lists_Hs {A : Type} [Group A] [Finite A] {ga gb z : A} {p k nL nS kg nC : Nat}
    (hk : ¬ 2 ^ (k + 1) ∣ Nat.card (Subgroup.closure ({ga, gb} : Set A)))
    (hz : z ∈ Subgroup.closure ({ga, gb} : Set A)) (hzo : orderOf z = p) {U : Nat → A}
    (hUa : ∀ i < nL, ∃ j < nL, U j = ga * U i * ga⁻¹)
    (hUb : ∀ i < nL, ∃ j < nL, U j = gb * U i * gb⁻¹)
    {g1 g2 : Nat → A} (hg1 : ∀ c < nC, g1 c ∈ Subgroup.closure ({ga, gb} : Set A))
    (hg2 : ∀ c < nC, g2 c ∈ Subgroup.closure ({ga, gb} : Set A))
    (hsimp : ∀ c < nC, IsSimpleGroup ↥(Subgroup.closure ({g1 c, g2 c} : Set A)))
    (hncomm : ∀ c < nC, ¬ IsMulCommutative ↥(Subgroup.closure ({g1 c, g2 c} : Set A)))
    (hzH : ∀ c < nC, z ∈ Subgroup.closure ({g1 c, g2 c} : Set A))
    (h3 : ∀ c < nC, 3 ∣ Nat.card ↥(Subgroup.closure ({g1 c, g2 c} : Set A)))
    (hW : ∀ i < nL, (∃ e : Nat, ∃ j < nL, U j = z ^ e * U i * (z ^ e)⁻¹ ∧
        U i * U j ≠ U j * U i) ∨
      ∃ c < nC, ∀ g ∈ ({g1 c, g2 c} : Set A), ∀ e < p, g * (z ^ e * U i * (z ^ e)⁻¹) * g⁻¹ ∈
        Subgroup.closure {x | x ∈ (List.range p).map (fun e => z ^ e * U i * (z ^ e)⁻¹)})
    {gG : Nat → A} (hG : ∀ j < kg, gG j ∈ Subgroup.closure ({ga, gb} : Set A)) {Ev : Nat → A}
    (hnS : nS = 2 ^ k) (hEv : ∀ i < nS, Ev i ∈ Subgroup.closure {x | ∃ j < kg, x = gG j})
    (hmul : ∀ i < nS, ∀ j < kg, ∃ R < nS, Ev R = Ev i * gG j)
    (hinj : ∀ i < nS, ∀ i' < nS, Ev i = Ev i' → i = i')
    (hinv : ∀ i < nS, Ev i * Ev i = 1 → Ev i ≠ 1 → ∃ ix < nL, U ix = Ev i) :
    ZCW ↥(Subgroup.closure ({ga, gb} : Set A)) p := by
  classical
  set M := Subgroup.closure ({ga, gb} : Set A)
  set S := Subgroup.closure {x | ∃ j < kg, x = gG j}
  set E : Set A := Set.range (fun i : Fin nS => Ev i)
  have hEm : ∀ x ∈ E, ∀ j < kg, x * gG j ∈ E := by
    rintro _ ⟨i, rfl⟩ j hj
    obtain ⟨R, hR, e⟩ := hmul i i.2 j hj
    exact ⟨⟨R, hR⟩, e⟩
  have key : ∀ g ∈ S, ∀ x ∈ E, x * g ∈ E := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨j, hj, rfl⟩ := hs
      exact fun x hx => hEm x hx j hj
    | one => exact fun x hx => by simpa using hx
    | mul g h _ _ hg hh => exact fun x hx => by simpa [mul_assoc] using hh _ (hg x hx)
    | inv g _ hg => exact zc_mul_inv_mem_of_finite hg
  have hnS0 : 0 < nS := hnS ▸ Nat.two_pow_pos k
  have h1E : (1 : A) ∈ E := by
    have h0 : Ev 0 ∈ E := ⟨⟨0, hnS0⟩, rfl⟩
    simpa using key _ (S.inv_mem (hEv 0 hnS0)) _ h0
  have hSE : ∀ x, x ∈ S ↔ x ∈ E := fun x =>
    ⟨fun hx => by simpa using key x hx 1 h1E, by rintro ⟨i, rfl⟩; exact hEv i i.2⟩
  have hcardS : Nat.card S = nS := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hSE),
      Nat.card_range_of_injective (fun i i' e => Fin.ext (hinj i i.2 i' i'.2 e)), Nat.card_fin]
  have hSM : S ≤ M := (Subgroup.closure_le _).mpr (by rintro x ⟨j, hj, rfl⟩; exact hG j hj)
  have hS' : Nat.card (S.subgroupOf M) = 2 ^ k := by
    rw [← hnS, ← hcardS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  set O : Set A := Set.range (fun i : Fin nL => U i)
  have hOfin : O.Finite := Set.finite_range _
  have hOa : ∀ x ∈ O, ga * x * ga⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUa i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hOb : ∀ x ∈ O, gb * x * gb⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUb i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hO' : ∀ x ∈ List.ofFn (fun i : Fin nL => U i), ∀ g ∈ [ga, gb, ga⁻¹, gb⁻¹],
      g * x * g⁻¹ ∈ List.ofFn (fun i : Fin nL => U i) := by
    intro x hx g hg
    rw [List.mem_ofFn] at hx ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact hOa x hx
    · exact hOb x hx
    · exact conj_inv_mem_of_finite hOfin hOa x hx
    · exact conj_inv_mem_of_finite hOfin hOb x hx
  have hOconj := zc_conj_mem_of_closure hO'
  have hord : orderOf (⟨z, hz⟩ : M) = p := by rw [Subgroup.orderOf_mk]; exact hzo
  unfold ZCW
  refine ⟨⟨z, hz⟩, hord, fun u hu hu1 => ?_⟩
  obtain ⟨g, hg⟩ := zc_exists_conj_mem_of_card (S.subgroupOf M) k hS' hk hu
  have hgS : (g : A) * u * (g : A)⁻¹ ∈ S := by simpa using Subgroup.mem_subgroupOf.mp hg
  obtain ⟨⟨i, hi⟩, hie⟩ := (hSE _).mp hgS
  have hie' : Ev i = (g : A) * u * (g : A)⁻¹ := hie
  have hu' : (u : A) * u = 1 := by simpa using congrArg Subtype.val hu
  have hss : Ev i * Ev i = 1 := by
    rw [hie']
    have e : (g : A) * u * (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) =
        (g : A) * ((u : A) * u) * (g : A)⁻¹ := by group
    rw [e, hu', mul_one, mul_inv_cancel]
  have hs1 : Ev i ≠ 1 := by
    rw [hie']
    intro e
    apply hu1
    apply Subtype.ext
    have e2 : (u : A) = (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) * g := by group
    rw [e2, e]
    simp
  obtain ⟨ix, hix, hUix⟩ := hinv i hi hss hs1
  have hmemO : (u : A) ∈ List.ofFn (fun i : Fin nL => U i) := by
    have h := hOconj ((g : A)⁻¹) (M.inv_mem g.2) (U ix) (List.mem_ofFn.2 ⟨⟨ix, hix⟩, rfl⟩)
    have e : (g : A)⁻¹ * ((g : A) * u * (g : A)⁻¹) * (g : A)⁻¹⁻¹ = u := by group
    rwa [hUix, hie', e] at h
  obtain ⟨⟨i', hi'⟩, hi'e⟩ := List.mem_ofFn.1 hmemO
  have hi'e' : U i' = u := hi'e
  rcases hW i' hi' with ⟨e, j, hj, hUj, hne⟩ | ⟨c, hc, hH⟩
  ·
    left
    refine ⟨1, Subgroup.one_mem _, ⟨z, hz⟩ ^ e, pow_mem (Subgroup.mem_zpowers _) e,
      fun heq => hne ?_⟩
    have h2 := congrArg Subtype.val heq
    simp only [one_mul, inv_one, mul_one, Subgroup.coe_mul, Subgroup.coe_inv,
      SubgroupClass.coe_pow, Subgroup.coe_mk] at h2
    rw [hUj, hi'e']
    exact h2
  ·
    right
    rw [hi'e'] at hH
    set cs : List A := (List.range p).map (fun e => z ^ e * (u : A) * (z ^ e)⁻¹)
    have hcs : ∀ x, x ∈ cs ↔ ∃ i < p, x = z ^ i * (u : A) * (z ^ i)⁻¹ := fun x => by
      simp only [cs, List.mem_map, List.mem_range]
      exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩, fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩⟩
    set K := Subgroup.closure ({g1 c, g2 c} : Set A)
    have hHN : K ≤ Subgroup.normalizer (Subgroup.closure {c | c ∈ cs} : Set A) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact mem_normalizer_conj_closure (hH x hx)
    have hHM : K ≤ M := by
      rw [Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact hg1 c hc
      · rw [Set.mem_singleton_iff.mp hx]
        exact hg2 c hc
    have hV := zc_mem_zConjClosure_iff hz u.2 hord cs hcs
    refine ⟨K.subgroupOf M, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxN : (x : A) ∈ Subgroup.normalizer (Subgroup.closure {c | c ∈ cs} : Set A) :=
        hHN (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.mem_normalizer_iff]
      intro v
      rw [hV v, hV (x * v * x⁻¹)]
      simpa using Subgroup.mem_normalizer_iff.mp hxN (v : A)
    · exact (MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hHM)).mpr (hsimp c hc)
    · intro hcomm
      apply hncomm c hc
      rw [isMulCommutative_iff] at hcomm ⊢
      intro x y
      apply (Subgroup.subgroupOfEquivOfLe hHM).symm.injective
      rw [map_mul, map_mul]
      exact hcomm _ _
    · exact Subgroup.mem_subgroupOf.mpr (hzH c hc)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
      exact h3 c hc

end CFSG.KC.EnumSound

end
