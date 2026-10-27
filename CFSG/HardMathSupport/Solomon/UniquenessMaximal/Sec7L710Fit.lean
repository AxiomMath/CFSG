module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710FitA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem comm_mem_pOf_iff {B T I : Subgroup G} {x y : G} (hx : x ∈ yOf B T I)
    (hy : y ∈ yOf B T I) :
    x * y * x⁻¹ * y⁻¹ ∈ pOf B T I ↔
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I)) ⟨x, hx⟩) *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I)) ⟨y, hy⟩) *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I)) ⟨x, hx⟩)⁻¹ *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I)) ⟨y, hy⟩)⁻¹ = 1 := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨z, hz, hzv⟩
    have : z = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := Subtype.ext (by simpa using hzv)
    exact this ▸ hz
  · intro h
    exact ⟨_, h, by simp⟩


private theorem mem_pOf_of_central {B T I : Subgroup G} (h : Setup710 B T I) {i : G} (hi : i ∈ I)
    (hc : ∀ j ∈ I, i * j * i⁻¹ * j⁻¹ ∈ pOf B T I) : i ∈ pOf B T I := by
  obtain ⟨hs, a, c, hac⟩ := isSimpleGroup_of_isLThreeFour h.lthree
  have := hs
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) with hπ
  have hz : π ⟨i, hi⟩ ∈ Subgroup.center (↥I ⧸ GLAPPrimeCore 3 ↥I) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : i * j * i⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
      rw [← inf_pOf_eq h]
      refine ⟨?_, hc j j.2⟩
      exact I.mul_mem (I.mul_mem (I.mul_mem hi j.2) (I.inv_mem hi)) (I.inv_mem j.2)
    obtain ⟨z, hz, hzv⟩ := h1
    have hzeq : z = ⟨i, hi⟩ * j * ⟨i, hi⟩⁻¹ * j⁻¹ := Subtype.ext (by simpa using hzv)
    rw [hzeq] at hz
    have h2 : π (⟨i, hi⟩ * j * ⟨i, hi⟩⁻¹ * j⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hz
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : π j * π ⟨i, hi⟩ = π ⟨i, hi⟩ * π j :=
      (commutatorElement_eq_one_iff_mul_comm.1 (by simpa [commutatorElement_def] using h2)).symm
    exact h3
  have hbot : Subgroup.center (↥I ⧸ GLAPPrimeCore 3 ↥I) = ⊥ := by
    rcases (inferInstance : (Subgroup.center (↥I ⧸ GLAPPrimeCore 3 ↥I)).Normal).eq_bot_or_eq_top
      with h' | h'
    · exact h'
    · exfalso
      have := Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c :
        c ∈ Subgroup.center (↥I ⧸ GLAPPrimeCore 3 ↥I)) a
      exact hac this
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz
  have : i ∈ GLAPPrimeCoreOf 3 I := ⟨_, hz, rfl⟩
  exact (inf_pOf_eq h ▸ this : i ∈ I ⊓ pOf B T I).2

theorem comm_mem_pOf_of_centralizes {B T I : Subgroup G} (h : Setup710 B T I) {b : G} (hb : b ∈ B)
    (hbI : ∀ i ∈ I, b * i * b⁻¹ * i⁻¹ ∈ pOf B T I) :
    ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ pOf B T I := by
  classical
  set Y := yOf B T I with hY
  set K := GLAPPrimeCore 3 ↥Y with hK
  set ρ := QuotientGroup.mk' K with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective K
  have hIY : I ≤ Y := I_le_yOf B T I
  have hTY : T ≤ Y := T_le_yOf B T I
  have hBY : B ≤ Y := B_le_yOf B T I
  set Nh : Subgroup (↥Y ⧸ K) := (I.subgroupOf Y).map ρ with hNh
  set Th : Subgroup (↥Y ⧸ K) := (T.subgroupOf Y).map ρ with hTh
  set Bh : Subgroup (↥Y ⧸ K) := (B.subgroupOf Y).map ρ with hBh
  have hInY : (I.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIY).2 (y_le_normalizer_I h)
  have hNn : Nh.Normal := Subgroup.Normal.map hInY ρ hρs
  have hmemN : ∀ i (hi : i ∈ I), ρ ⟨i, hIY hi⟩ ∈ Nh := fun i hi =>
    Subgroup.mem_map_of_mem ρ ((Subgroup.mem_subgroupOf).2 hi)
  have hmemT : ∀ i (hi : i ∈ T), ρ ⟨i, hTY hi⟩ ∈ Th := fun i hi =>
    Subgroup.mem_map_of_mem ρ ((Subgroup.mem_subgroupOf).2 hi)
  have hmemB : ∀ i (hi : i ∈ B), ρ ⟨i, hBY hi⟩ ∈ Bh := fun i hi =>
    Subgroup.mem_map_of_mem ρ ((Subgroup.mem_subgroupOf).2 hi)
  have hNc : ∀ x ∈ Nh, (∀ n ∈ Nh, x * n = n * x) → x = 1 := by
    intro x hx hcx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyI : (y : G) ∈ I := (Subgroup.mem_subgroupOf).1 hy
    have hP : (y : G) ∈ pOf B T I := by
      refine mem_pOf_of_central h hyI fun j hj => ?_
      have := hcx _ (hmemN j hj)
      have := (comm_mem_pOf_iff (B := B) (T := T) (I := I) y.2 (hIY hj)).2 (by
        have h2 := commutatorElement_eq_one_iff_mul_comm.2 this
        exact (commutatorElement_def _ _).symm.trans h2)
      exact this
    obtain ⟨z, hz, hzv⟩ := hP
    have : z = y := Subtype.ext hzv
    rw [this] at hz
    exact (QuotientGroup.eq_one_iff _).2 hz
  have hQ : ∀ q : ↥Y ⧸ K, q ∈ Nh ⊔ Th ⊔ Bh := by
    intro q
    obtain ⟨y, rfl⟩ := hρs q
    obtain ⟨i, hi, t, ht, c, hc, hy⟩ := exists_mul_of_mem_yOf h y.2
    have : y = ⟨i, hIY hi⟩ * ⟨t, hTY ht⟩ * ⟨c, hBY hc⟩ := Subtype.ext hy
    rw [this, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hmemN i hi)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hmemT t ht))))
      (Subgroup.mem_sup_right (hmemB c hc))
  have hT2 : IsPGroup 2 ↥Th :=
    IsPGroup.map (h.tTwo.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm) ρ
  have hB3 : IsPGroup 3 ↥Bh := by
    have hB3' : IsPGroup 3 ↥B := IsPGroup.of_card (n := 4) (by rw [h.card_b]; norm_num)
    exact IsPGroup.map (hB3'.of_equiv (Subgroup.subgroupOfEquivOfLe hBY).symm) ρ
  have hBi : ¬ 3 ∣ Bh.index := fun hd =>
    b_sylow_y h (hd.trans (Subgroup.index_map_dvd (B.subgroupOf Y) hρs))
  have hconj : ∀ g ∈ Bh, ∀ x ∈ Th, g * x * g⁻¹ ∈ Th := by
    rintro _ ⟨b', hb', rfl⟩ _ ⟨t', ht', rfl⟩
    refine ⟨b' * t' * b'⁻¹, ?_, by simp⟩
    have hb'' : (b' : G) ∈ B := (Subgroup.mem_subgroupOf).1 hb'
    have ht'' : (t' : G) ∈ T := (Subgroup.mem_subgroupOf).1 ht'
    exact (Subgroup.mem_subgroupOf).2 ((Subgroup.mem_normalizer_iff.1 (h.bnT hb'') _).1 ht'')
  have hBT : Bh ≤ Subgroup.normalizer (Th : Set (↥Y ⧸ K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj g hg x hx, fun hx => ?_⟩
    have := hconj g⁻¹ (Bh.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hcore : GLAPPrimeCore 3 (↥Y ⧸ K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hbN : ∀ n ∈ Nh, ρ ⟨b, hBY hb⟩ * n = n * ρ ⟨b, hBY hb⟩ := by
    rintro _ ⟨i, hi, rfl⟩
    have hiI : (i : G) ∈ I := (Subgroup.mem_subgroupOf).1 hi
    have := (comm_mem_pOf_iff (B := B) (T := T) (I := I) (hBY hb) i.2).1 (hbI _ hiI)
    exact commutatorElement_eq_one_iff_mul_comm.1 ((commutatorElement_def _ _).trans this)
  intro t ht
  have key := commutes_of_centralizes_normal Nh Th Bh hNc hQ hT2 hB3 hBi hBT hcore
    (hmemB b hb) hbN (ρ ⟨t, hTY ht⟩) (hmemT t ht)
  exact (comm_mem_pOf_iff (B := B) (T := T) (I := I) (hBY hb) (hTY ht)).2 key

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
