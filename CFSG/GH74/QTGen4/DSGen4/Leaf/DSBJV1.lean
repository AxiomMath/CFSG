module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBJV1

variable {G : Type} [Group G]




theorem mem_conj_map_iff {X : Subgroup G} {y x : G} :
    x ∈ X.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * x * y ∈ X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨y⁻¹ * x * y, h, by simp [mul_assoc]⟩

theorem coset_mem {S R : Subgroup G} {t : G} (hi : R.relIndex S = 2) (ht : t ∈ S)
    (htR : t ∉ R) : (∀ s ∈ S, s ∈ R ∨ t⁻¹ * s ∈ R) ∧ t * t ∈ R := by
  have hi' : (R.subgroupOf S).index = 2 := hi
  have hmul : ∀ a b : S, a * b ∈ R.subgroupOf S ↔ (a ∈ R.subgroupOf S ↔ b ∈ R.subgroupOf S) :=
    fun a b => Subgroup.mul_mem_iff_of_index_two hi'
  constructor
  · intro s hs
    by_cases hsR : s ∈ R
    · exact Or.inl hsR
    · right
      have hL : (⟨t⁻¹, S.inv_mem ht⟩ * ⟨s, hs⟩ : S) ∈ R.subgroupOf S := by
        rw [hmul]
        simp [Subgroup.mem_subgroupOf, htR, hsR]
      exact Subgroup.mem_subgroupOf.mp hL
  · have hL : (⟨t, ht⟩ * ⟨t, ht⟩ : S) ∈ R.subgroupOf S := by
      rw [hmul]
    exact Subgroup.mem_subgroupOf.mp hL

theorem exists_mem_not_mem {S R : Subgroup G} (hRS : R ≤ S) (hi : R.relIndex S = 2) :
    ∃ t ∈ S, t ∉ R := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have hSR : S ≤ R := fun s hs => by
    by_contra hsR
    exact hc s hs hsR
  have hEq : R = S := le_antisymm hRS hSR
  rw [hEq, Subgroup.relIndex_self] at hi
  norm_num at hi

theorem core_of_comm_outside {S R Z2 Z : Subgroup G} (hRS : R ≤ S) (hi : R.relIndex S = 2)
    (hZ2R : ∀ z ∈ Z2, ∀ r ∈ R, r * z = z * r)
    (hZch : ∀ a ∈ S, (∀ s ∈ S, s * a = a * s) → a ^ 2 = 1 → a ∈ Z)
    (hZ2el : ∀ z ∈ Z2, z ^ 2 = 1) (hZ2S : Z2 ≤ S) :
    ∀ a ∈ Z2, ∀ w ∈ S, w ∉ R → w * a = a * w → a ∈ Z := by
  intro a ha w hw hwR hwa
  obtain ⟨t, ht, htR⟩ := exists_mem_not_mem hRS hi
  obtain ⟨hcos, -⟩ := coset_mem hi ht htR
  have hr : t⁻¹ * w ∈ R := (hcos w hw).resolve_left hwR
  have hwr : t * (t⁻¹ * w) = w := by group
  have h1 : a * (t * (t⁻¹ * w)) = (t * (t⁻¹ * w)) * a := by
    rw [hwr, hwa]
  have hra : (t⁻¹ * w) * a = a * (t⁻¹ * w) := hZ2R a ha _ hr
  have h2 : (a * t) * (t⁻¹ * w) = (t * a) * (t⁻¹ * w) := by
    calc (a * t) * (t⁻¹ * w) = a * (t * (t⁻¹ * w)) := by simp only [mul_assoc]
      _ = (t * (t⁻¹ * w)) * a := h1
      _ = t * ((t⁻¹ * w) * a) := by simp only [mul_assoc]
      _ = t * (a * (t⁻¹ * w)) := by rw [hra]
      _ = (t * a) * (t⁻¹ * w) := by simp only [mul_assoc]
  have hat : a * t = t * a := mul_right_cancel h2
  apply hZch a (hZ2S ha)
  · intro s hs
    by_cases hsR : s ∈ R
    · exact hZ2R a ha s hsR
    · have hr' : t⁻¹ * s ∈ R := (hcos s hs).resolve_left hsR
      have hra' : (t⁻¹ * s) * a = a * (t⁻¹ * s) := hZ2R a ha _ hr'
      calc s * a = t * ((t⁻¹ * s) * a) := by group
        _ = t * (a * (t⁻¹ * s)) := by rw [hra']
        _ = (t * a) * (t⁻¹ * s) := by group
        _ = (a * t) * (t⁻¹ * s) := by rw [hat]
        _ = a * s := by group
  · exact hZ2el a ha

theorem comm_mem_of_gen {T : Set G} {H Z : Subgroup G} (hH : Subgroup.closure T = H)
    (hZc : ∀ c ∈ Z, ∀ x ∈ H, c * x = x * c)
    (hT : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ Z) :
    ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ Z := by
  have key : ∀ a ∈ T, ∀ b ∈ H, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    rw [← hH] at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx => exact hT a ha x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxH : x ∈ H := hH ▸ hx
      have hyc : ⁅a, y⁆ * x = x * ⁅a, y⁆ := hZc _ ihy x hxH
      have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have hxd : x * ⁅a, y⁆ * x⁻¹ = ⁅a, y⁆ := by
        rw [← hyc]; group
      rw [e, hxd]
      exact Z.mul_mem ihx ihy
    | inv x hx ihx =>
      have hxH : x ∈ H := hH ▸ hx
      have hcx : ⁅a, x⁆ * x = x * ⁅a, x⁆ := hZc _ ihx x hxH
      have hcx' : ⁅a, x⁆⁻¹ * x = x * ⁅a, x⁆⁻¹ :=
        (Commute.inv_left (show Commute ⁅a, x⁆ x from hcx)).eq
      have e : ⁅a, x⁻¹⁆ = x⁻¹ * ⁅a, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have : ⁅a, x⁻¹⁆ = ⁅a, x⁆⁻¹ := by
        rw [e, mul_assoc, hcx', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Z.inv_mem ihx
  have hgen : ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ Z := by
    intro a ha
    rw [← hH] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact fun b hb => key x hx b hb
    | one => intro b _; simp
    | mul x y hx hy ihx ihy =>
      intro b hb
      have hxH : x ∈ H := hH ▸ hx
      have hyc : ⁅y, b⁆ * x = x * ⁅y, b⁆ := hZc _ (ihy b hb) x hxH
      have e : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
        simp only [commutatorElement_def]; group
      have hxd : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by
        rw [← hyc]; group
      rw [e, hxd]
      exact Z.mul_mem (ihy b hb) (ihx b hb)
    | inv x hx ihx =>
      intro b hb
      have hxH : x ∈ H := hH ▸ hx
      have hcx : ⁅x, b⁆ * x = x * ⁅x, b⁆ := hZc _ (ihx b hb) x hxH
      have hcx' : ⁅x, b⁆⁻¹ * x = x * ⁅x, b⁆⁻¹ :=
        (Commute.inv_left (show Commute ⁅x, b⁆ x from hcx)).eq
      have e : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have : ⁅x⁻¹, b⁆ = ⁅x, b⁆⁻¹ := by
        rw [e, mul_assoc, hcx', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Z.inv_mem (ihx b hb)
  exact hgen

theorem sq_mem_of_gen {T : Set G} {H Z : Subgroup G} (hH : Subgroup.closure T = H)
    (hZc : ∀ c ∈ Z, ∀ x ∈ H, c * x = x * c)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ Z) (hT : ∀ a ∈ T, a ^ 2 ∈ Z) :
    ∀ a ∈ H, a ^ 2 ∈ Z := by
  intro a ha
  rw [← hH] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hT x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxH : x ∈ H := hH ▸ hx
    have hyH : y ∈ H := hH ▸ hy
    have hc : ⁅y⁻¹, x⁻¹⁆ ∈ Z := hcomm y⁻¹ (H.inv_mem hyH) x⁻¹ (H.inv_mem hxH)
    have hcy : ⁅y⁻¹, x⁻¹⁆ * y = y * ⁅y⁻¹, x⁻¹⁆ := hZc _ hc y hyH
    have hyx : y * x = x * y * ⁅y⁻¹, x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have e : (x * y) ^ 2 = x ^ 2 * (⁅y⁻¹, x⁻¹⁆ * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by simp only [pow_two, mul_assoc]
        _ = x * (x * y * ⁅y⁻¹, x⁻¹⁆) * y := by rw [hyx]
        _ = x ^ 2 * (y * ⁅y⁻¹, x⁻¹⁆ * y) := by simp only [pow_two, mul_assoc]
        _ = x ^ 2 * (⁅y⁻¹, x⁻¹⁆ * y ^ 2) := by rw [← hcy]; simp only [pow_two, mul_assoc]
    rw [e]
    exact Z.mul_mem ihx (Z.mul_mem hc ihy)
  | inv x hx ihx =>
    rw [inv_pow]
    exact Z.inv_mem ihx

theorem dsFrattini_le_of_comm_sq [Finite G] {V Z : Subgroup G} (hV : IsPGroup 2 V)
    (hc : ⁅V, V⁆ ≤ Z) (hs : ∀ v ∈ V, v ^ 2 ∈ Z) : dsFrattini V ≤ Z := by
  haveI : Fact (IsPGroup 2 ↥V) := ⟨hV⟩
  unfold dsFrattini
  rw [Subgroup.map_le_iff_le_comap]
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  rw [Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have key : ∀ g h : ↥V, ⁅g, h⁆ ∈ Z.comap V.subtype := fun g h => by
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact hc (Subgroup.commutator_mem_commutator g.2 h.2)
    have hc' : (⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆) ≤ Z.comap V.subtype :=
      Subgroup.commutator_le.mpr (fun g _ h _ => key g h)
    exact hc' hx
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa using hs y.1 y.2

theorem core_central {S R Z2 Z : Subgroup G} (hRS : R ≤ S) (hi : R.relIndex S = 2)
    (hZ2R : ∀ z ∈ Z2, ∀ r ∈ R, r * z = z * r)
    (hZch : ∀ a ∈ S, (∀ s ∈ S, s * a = a * s) → a ^ 2 = 1 → a ∈ Z)
    (hZ2el : ∀ z ∈ Z2, z ^ 2 = 1) (hZ2n : ∀ z ∈ Z2, ∀ s ∈ S, s⁻¹ * z * s ∈ Z2)
    (hZ2S : Z2 ≤ S) :
    ∀ z ∈ Z2, ∀ s ∈ S, ⁅z, s⁆ ∈ Z := by
  intro z hz s hs
  obtain ⟨t, ht, htR⟩ := exists_mem_not_mem hRS hi
  obtain ⟨hcos, htt⟩ := coset_mem hi ht htR
  have hv : t * z * t⁻¹ ∈ Z2 := by
    have := hZ2n z hz t⁻¹ (S.inv_mem ht)
    simpa [mul_assoc] using this
  have hz' : t⁻¹ * t⁻¹ * z * (t * t) = z := by
    calc t⁻¹ * t⁻¹ * z * (t * t) = (t⁻¹ * t⁻¹) * (z * (t * t)) := by group
      _ = (t⁻¹ * t⁻¹) * ((t * t) * z) := by rw [(hZ2R z hz (t * t) htt).symm]
      _ = z := by group
  have huv : t⁻¹ * z * t = t * z * t⁻¹ := by
    calc t⁻¹ * z * t = t * (t⁻¹ * t⁻¹ * z * (t * t)) * t⁻¹ := by group
      _ = t * z * t⁻¹ := by rw [hz']
  have hwdef : ⁅z, t⁆ = z * (t * z⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def]; group
  have hwZ2 : ⁅z, t⁆ ∈ Z2 := by
    rw [hwdef]
    exact Z2.mul_mem hz (by simpa [mul_assoc] using hZ2n z⁻¹ (Z2.inv_mem hz) t⁻¹ (S.inv_mem ht))
  have hwsq : ⁅z, t⁆ ^ 2 = 1 := hZ2el _ hwZ2
  have hwinv : (⁅z, t⁆)⁻¹ = ⁅z, t⁆ :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hwsq)
  have e1 : t⁻¹ * ⁅z, t⁆ * t = (⁅z, t⁆)⁻¹ := by
    rw [hwdef]
    calc t⁻¹ * (z * (t * z⁻¹ * t⁻¹)) * t = (t⁻¹ * z * t) * z⁻¹ := by group
      _ = (t * z * t⁻¹) * z⁻¹ := by rw [huv]
      _ = (z * (t * z⁻¹ * t⁻¹))⁻¹ := by group
  have hconj : t⁻¹ * ⁅z, t⁆ * t = ⁅z, t⁆ := by rw [e1, hwinv]
  have hwt : ⁅z, t⁆ * t = t * ⁅z, t⁆ := by
    calc ⁅z, t⁆ * t = t * (t⁻¹ * ⁅z, t⁆ * t) := by group
      _ = t * ⁅z, t⁆ := by rw [hconj]
  have hcomm : ∀ s ∈ S, s * ⁅z, t⁆ = ⁅z, t⁆ * s := by
    intro s hs
    by_cases hsR : s ∈ R
    · exact hZ2R _ hwZ2 s hsR
    · have hr' : t⁻¹ * s ∈ R := (hcos s hs).resolve_left hsR
      have hrw : (t⁻¹ * s) * ⁅z, t⁆ = ⁅z, t⁆ * (t⁻¹ * s) := hZ2R _ hwZ2 _ hr'
      calc s * ⁅z, t⁆ = t * ((t⁻¹ * s) * ⁅z, t⁆) := by group
        _ = t * (⁅z, t⁆ * (t⁻¹ * s)) := by rw [hrw]
        _ = (t * ⁅z, t⁆) * (t⁻¹ * s) := by group
        _ = (⁅z, t⁆ * t) * (t⁻¹ * s) := by rw [hwt]
        _ = ⁅z, t⁆ * s := by group
  have hwZ : ⁅z, t⁆ ∈ Z := hZch _ (hZ2S hwZ2) hcomm hwsq
  by_cases hsR : s ∈ R
  · have h1 : ⁅z, s⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hZ2R z hz s hsR).symm
    rw [h1]; exact Z.one_mem
  · obtain ⟨r, hrR, rfl⟩ : ∃ r ∈ R, s = t * r :=
      ⟨t⁻¹ * s, (hcos s hs).resolve_left hsR, by group⟩
    have hzr : r * z = z * r := hZ2R z hz r hrR
    have hzinv : r * z⁻¹ = z⁻¹ * r := (Commute.inv_right (show Commute r z from hzr)).eq
    have e : ⁅z, t * r⁆ = ⁅z, t⁆ := by
      simp only [commutatorElement_def]
      calc z * (t * r) * z⁻¹ * (t * r)⁻¹ = z * t * (r * z⁻¹) * r⁻¹ * t⁻¹ := by group
        _ = z * t * (z⁻¹ * r) * r⁻¹ * t⁻¹ := by rw [hzinv]
        _ = z * t * z⁻¹ * t⁻¹ := by group
    rw [e]; exact hwZ

theorem dsConjClosure_eq_closure (Y X : Subgroup G) :
    dsConjClosure Y X = Subgroup.closure (⋃ y ∈ Y, ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) := by
  apply le_antisymm
  · unfold dsConjClosure
    refine iSup₂_le fun y hy => ?_
    intro x hx
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion]
    exact ⟨y, hy, hx⟩
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hx⟩ := hx
    unfold dsConjClosure
    exact (le_iSup₂ (f := fun y (_ : y ∈ Y) => X.map (MulAut.conj y).toMonoidHom) y hy) hx

theorem central_of_gen {T : Set G} {H : Subgroup G} (hH : Subgroup.closure T = H) {z : G}
    (hz : ∀ t ∈ T, z * t = t * z) : ∀ x ∈ H, z * x = x * z := by
  intro x hx
  rw [← hH] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hz x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    calc z * (x * y) = (z * x) * y := by group
      _ = (x * z) * y := by rw [ihx]
      _ = x * (z * y) := by group
      _ = x * (y * z) := by rw [ihy]
      _ = x * y * z := by group
  | inv x _ ihx =>
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [ihx]
      _ = x⁻¹ * z := by group
      _ = x⁻¹ * z := rfl

theorem comm_with_normal_of_gen {T : Set G} {H N : Subgroup G} (hH : Subgroup.closure T = H)
    (hNn : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (q : G) (hT : ∀ a ∈ T, ⁅q, a⁆ ∈ N) :
    ∀ e ∈ H, ⁅q, e⁆ ∈ N := by
  intro e he
  rw [← hH] at he
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hT x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxH : x ∈ H := hH ▸ hx
    have e1 : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact N.mul_mem ihx (hNn x hxH _ ihy)
  | inv x hx ihx =>
    have hxH : x ∈ H := hH ▸ hx
    have e1 : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact hNn x⁻¹ (H.inv_mem hxH) _ (N.inv_mem ihx)




theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have := isMulCommutative_iff.mp hE.1 ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsPGroup 2 ↥E := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using hE.2 g.1 g.2

theorem dsOmega1_le (X : Subgroup G) : CFSG.GH74.QTGen4.DSGen4.dsOmega1 X ≤ X := by
  unfold CFSG.GH74.QTGen4.DSGen4.dsOmega1
  rw [Subgroup.closure_le]
  exact fun _ hx => hx.1

theorem comm_closure {T : Set G} {H : Subgroup G} (hH : Subgroup.closure T = H)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have hT1 : ∀ a ∈ T, ∀ b ∈ H, a * b = b * a := by
    intro a ha
    exact central_of_gen hH (fun t ht => hT a ha t ht)
  intro a ha
  rw [← hH] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact fun b hb => hT1 x hx b hb
  | one => intro b _; simp
  | mul x y hx hy ihx ihy =>
    intro b hb
    calc x * y * b = x * (y * b) := by group
      _ = x * (b * y) := by rw [ihy b hb]
      _ = (x * b) * y := by group
      _ = (b * x) * y := by rw [ihx b hb]
      _ = b * (x * y) := by group
  | inv x hx ihx =>
    intro b hb
    have hxb : x * b = b * x := ihx b hb
    have hxH : x ∈ H := hH ▸ hx
    calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * b) * x⁻¹ := by rw [hxb]
      _ = b * x⁻¹ := by group

theorem conj_comm {Z2 : Subgroup G} (hE : IsElemAbelian 2 Z2) (y : G) {a b : G}
    (ha : a ∈ Z2.map (MulAut.conj y).toMonoidHom) (hb : b ∈ Z2.map (MulAut.conj y).toMonoidHom) :
    a * b = b * a := by
  rw [mem_conj_map_iff] at ha hb
  have h := comm_of_isElemAbelian hE ha hb
  calc a * b = y * (y⁻¹ * a * y) * (y⁻¹ * b * y) * y⁻¹ := by group
    _ = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [h]
    _ = b * a := by group

theorem le_dsConjClosure {P Z2 : Subgroup G} (h1 : (1 : G) ∈ P) :
    Z2 ≤ CFSG.GH74.QTGen4.DSGen4.dsConjClosure P Z2 := by
  intro z hz
  have hz1 : z ∈ Z2.map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [mem_conj_map_iff]; simpa using hz
  unfold CFSG.GH74.QTGen4.DSGen4.dsConjClosure
  exact (le_iSup₂ (f := fun (y : G) (_ : y ∈ P) => Z2.map (MulAut.conj y).toMonoidHom)
    (1 : G) h1) hz1

theorem dsConjClosure_le {P Z2 K : Subgroup G} (h : ∀ y ∈ P, Z2.map (MulAut.conj y).toMonoidHom ≤ K) :
    CFSG.GH74.QTGen4.DSGen4.dsConjClosure P Z2 ≤ K := by
  unfold CFSG.GH74.QTGen4.DSGen4.dsConjClosure
  exact iSup₂_le fun y hy => h y hy

theorem conj_mem_of_normalizer {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {h : G} (hh : h ∈ H) : g * h * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg h).mp hh

theorem exists_not_mem_of_not_le {G : Type} [Group G] {A B : Subgroup G} (h : ¬ A ≤ B) :
    ∃ z ∈ A, z ∉ B := by
  by_contra hc
  push Not at hc
  exact h (fun z hz => hc z hz)

theorem isPGroup_of_le_of {G : Type} [Group G] {p : ℕ} {H K : Subgroup G} (hK : IsPGroup p K)
    (h : H ≤ K) : IsPGroup p H := by
  intro g
  obtain ⟨k, hk⟩ := hK ⟨g, h g.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hk
  simpa using this



theorem borel_index_five {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G}
    (h : DSBHyp L1 L2 S) (hQL1 : dsQ L1 L2 S ≤ L1) (hPB : ¬ (L1 ⊔ bigB L1 L2 S) ≤ bigB L1 L2 S) :
    (borelOf L1 S).relIndex L1 = 5 := by
  have hA5 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := hA5.quot
  have hsyl : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  obtain ⟨⟨d, hdB, hd3⟩, hcardS1⟩ := DSBA5.three_and_card hsyl hq1
  have hpc : pCoreOf 2 L1 = dsQ L1 L2 S := by
    rw [← F1.inf_pCoreOf_parabolic_eq h.hyp]
    exact inf_eq_left.mpr hQL1
  have hcardQuot : Nat.card (oTwoQuot ↥L1) = 60 := by
    rw [IsL2Quot.card (by norm_num) hq1]; norm_num
  have hcardN : Nat.card ↥(pCoreOf 2 L1) = Nat.card ↥(CFSG.Open.pCore 2 ↥L1) :=
    Subgroup.card_map_of_injective L1.subtype_injective
  have hL1card : Nat.card ↥L1 = 60 * Nat.card ↥(pCoreOf 2 L1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L1), hcardN,
      ← hcardQuot]
  have hqpos : 0 < Nat.card ↥(pCoreOf 2 L1) := Nat.card_pos
  have hH : Nat.card ↥(S ⊓ L1) = 4 * Nat.card ↥(pCoreOf 2 L1) := hcardS1
  have hidx15 : ((S ⊓ L1).subgroupOf L1).index = 15 := by
    have h1 := Subgroup.card_mul_index ((S ⊓ L1).subgroupOf L1)
    have h2 : Nat.card ↥((S ⊓ L1).subgroupOf L1) = Nat.card ↥(S ⊓ L1) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h2, hH, hL1card] at h1
    have h3 : Nat.card ↥(pCoreOf 2 L1) * (4 * ((S ⊓ L1).subgroupOf L1).index) =
        Nat.card ↥(pCoreOf 2 L1) * 60 := by
      calc Nat.card ↥(pCoreOf 2 L1) * (4 * ((S ⊓ L1).subgroupOf L1).index)
          = 4 * Nat.card ↥(pCoreOf 2 L1) * ((S ⊓ L1).subgroupOf L1).index := by ring
        _ = 60 * Nat.card ↥(pCoreOf 2 L1) := h1
        _ = Nat.card ↥(pCoreOf 2 L1) * 60 := by ring
    have h4 := Nat.eq_of_mul_eq_mul_left hqpos h3
    omega
  have hHK : S ⊓ L1 ≤ borelOf L1 S := F1.sylow_le_borelOf L1 S
  have hKL : borelOf L1 S ≤ L1 := F1.borelOf_le L1 S
  have hmul : (S ⊓ L1).relIndex (borelOf L1 S) * (borelOf L1 S).relIndex L1 = 15 := by
    rw [← hidx15]
    exact Subgroup.relIndex_mul_relIndex _ _ _ hHK hKL
  have hcardK : Nat.card ↥(borelOf L1 S) =
      Nat.card ↥(S ⊓ L1) * (S ⊓ L1).relIndex (borelOf L1 S) := by
    have hK := Subgroup.card_mul_index ((S ⊓ L1).subgroupOf (borelOf L1 S))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at hK
    rw [← hK]
    rfl
  have h3K : 3 ∣ Nat.card ↥(borelOf L1 S) := by
    have h := orderOf_dvd_natCard (⟨d, hdB⟩ : ↥(borelOf L1 S))
    rw [Subgroup.orderOf_mk, hd3] at h
    exact h
  have hnot3 : ¬ 3 ∣ Nat.card ↥(S ⊓ L1) := by
    intro h3
    obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).mp hsyl.2.1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (dvd_trans h3 hn)) (by norm_num)
  have h3k : 3 ∣ (S ⊓ L1).relIndex (borelOf L1 S) := by
    rw [hcardK] at h3K
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3K with h | h
    · exact absurd h hnot3
    · exact h
  obtain ⟨m, hm⟩ := h3k
  rw [hm] at hmul
  have hmI : m * (borelOf L1 S).relIndex L1 = 5 := by
    have : 3 * (m * (borelOf L1 S).relIndex L1) = 3 * 5 := by linarith [hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hm5 : m ∣ 5 := ⟨_, hmI.symm⟩
  rcases (Nat.dvd_prime (by norm_num)).mp hm5 with hm1 | hm5'
  · rw [hm1, one_mul] at hmI; exact hmI
  · exfalso
    rw [hm5'] at hmI
    have hI1 : (borelOf L1 S).relIndex L1 = 1 := by omega
    have hle : L1 ≤ borelOf L1 S := Subgroup.relIndex_eq_one.mp hI1
    exact hPB (sup_le (hle.trans (le_sup_left.trans le_sup_left)) le_rfl)



theorem main_V [DSLeaf LeafDSBJZ2] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex]
    [DSLeaf LeafZiStructure] [DSLeaf LeafChiefOfA5] [DSLeaf LeafM3] [DSLeaf LeafM5]
    [DSLeaf LeafBruhat] [DSLeaf LeafRankBounds] [DSLeaf LeafSylowS] [DSLeaf LeafFaithfulA5]
    {G : Type} [Group G] [Finite4 G] {L1 L2 S : Subgroup G} (h : DSBHyp L1 L2 S)
    (cJ : ⁅dsZi L1 S, L1⁆ = ⊥) :
    Nat.card (dsZ S) = 2 ∧ A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsV1 L1 L2 S) (dsZ S) ∧
      ¬ NatSec L1 (dsZ S) (dsV1 L1 L2 S) ∧ ⁅dsV1 L1 L2 S, dsV1 L1 L2 S⁆ = dsZ S ∧
      dsV1 L1 L2 S ≤ dsQ L1 L2 S := by
  have hA5 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := hA5.quot
  have hPL1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := hA5.norm
  have hbnorm : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := DSBHyp.bnorm h
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, hbnorm⟩
  have hZS' : ZSetting L2 L1 S := hZS.symm
  obtain ⟨hZ0, -, -, -, -, hP1Z1, -⟩ := zi_structure hZS
  obtain ⟨-, hZZ2, -, hZ2el0, -, hP2Z2o, -⟩ := zi_structure hZS'
  obtain ⟨⟨-, -⟩, ⟨hJ2a, -, hJ2c, hJ2d, hJ2e⟩, hJ3⟩ := dsbjz2 h cJ
  obtain ⟨hS1, hQi, hQL1⟩ := dsba5_vertex h
  obtain ⟨hS2, hRi, -, -⟩ := dsbs3_vertex h
  obtain ⟨-, -, hQS⟩ := sylow_s h.hyp
  have hcJZ : dsZi L1 S = dsZ S := dsZi_eq_dsZ_of_commutator_eq_bot cJ
  have hPZ0 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsZ S : Set G) := by
    rw [← hcJZ]; exact hP1Z1
  have hZ2el0' : IsElemAbelian 2 (dsZi L2 S) := by rw [hJ2a]; exact hZ2el0
  have hZ2c0 : dsZi L2 S ≤ centerOf (dsQ L2 L1 S) := by rw [hJ2a]; exact dsOmega1_le _
  have hRdef : dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
    unfold dsQ; rw [bigB_comm]
  have hRN0 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := by
    rw [hRdef]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hP2Z2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := by
    have h0 := hP2Z2o; rw [bigB_comm] at h0; exact h0
  have hP2Z2o' : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (dsZi L2 S : Set G) := hP2Z2o
  set P : Subgroup G := L1 ⊔ bigB L1 L2 S with hPdef
  set B : Subgroup G := bigB L1 L2 S with hBdef
  set Q : Subgroup G := dsQ L1 L2 S with hQdef
  set R : Subgroup G := dsQ L2 L1 S with hRdef'
  set Z : Subgroup G := dsZ S with hZdef
  set Z2 : Subgroup G := dsZi L2 S with hZ2def
  set V : Subgroup G := dsV1 L1 L2 S with hVdef
  have hQS' : Q ≤ S := hQS
  have hRS : R ≤ S := by
    calc R ≤ (S ⊓ L2) ⊔ R := le_sup_right
      _ = S := hS2.symm
  have hRi' : R.relIndex S = 2 := hRi
  have hZ2S0 : Z2 ≤ Q := hJ3
  have hZ2S : Z2 ≤ S := hZ2S0.trans hQS'
  have hZ2c : Z2 ≤ centerOf R := hZ2c0
  have hZ2R : ∀ z ∈ Z2, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    Subgroup.mem_centralizer_iff.mp (hZ2c hz).2 r hr
  have hZ2el : IsElemAbelian 2 Z2 := hZ2el0'
  have hZ2sq : ∀ z ∈ Z2, z ^ 2 = 1 := fun z hz => hZ2el.2 z hz
  have hZ2R' : Z2 ≤ R := hZ2c.trans inf_le_left
  have hZZ2' : Z ≤ Z2 := hZZ2
  have hZ0' : Z ≠ ⊥ := hZ0
  have hSB : S ≤ B := le_sup_right
  have hSP2 : S ≤ L2 ⊔ B := hSB.trans le_sup_right
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := hPZ0
  have hP2Z : L2 ⊔ B ≤ Subgroup.normalizer (Z2 : Set G) := hP2Z2
  have hRN : L2 ⊔ B ≤ Subgroup.normalizer (R : Set G) := hRN0
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hZch : ∀ a ∈ S, (∀ s ∈ S, s * a = a * s) → a ^ 2 = 1 → a ∈ Z := fun a ha hc hsq =>
    Subgroup.subset_closure ⟨⟨ha, Subgroup.mem_centralizer_iff.mpr hc⟩, hsq⟩
  have hZ2n : ∀ z ∈ Z2, ∀ s ∈ S, s⁻¹ * z * s ∈ Z2 := fun z hz s hs => by
    have hsi : s⁻¹ ∈ Subgroup.normalizer (Z2 : Set G) :=
      hP2Z ((L2 ⊔ B).inv_mem (hSP2 hs))
    have := conj_mem_of_normalizer hsi hz
    simpa using this
  have hcore_S : ∀ z ∈ Z2, ∀ s ∈ S, ⁅z, s⁆ ∈ Z :=
    core_central hRS hRi' hZ2R hZch hZ2sq hZ2n hZ2S
  have hNP : (L1 ⊔ bigB L2 L1 S) ⊓ Subgroup.normalizer (Z2 : Set G) = bigB L2 L1 S := by
    apply normalizer_inf_eq_bigB h.hyp.symm
    · exact isPGroup_of_isElemAbelian hZ2el
    · exact hZ2S.trans le_sup_right
    · intro h0
      exact hZ0' (le_bot_iff.mp (hZZ2'.trans h0.le))
    · exact hP2Z2o'
  rw [bigB_comm] at hNP
  have hPstab : ∀ y ∈ P, y ∈ Subgroup.normalizer (Z2 : Set G) → y ∈ B := fun y hy hyN => by
    have hmem : y ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (Z2 : Set G) := ⟨hy, hyN⟩
    rw [hNP] at hmem
    exact hmem
  have hBP2 : B ≤ L2 ⊔ B := le_sup_right
  have hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (Z2 : Set G) := fun b hb => hP2Z (hBP2 hb)
  have hVgen : Subgroup.closure
      (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) = V :=
    (dsConjClosure_eq_closure P Z2).symm
  have hZ2V : Z2 ≤ V := le_dsConjClosure (Subgroup.one_mem P)
  have hCV : ∀ y ∈ P, Z2.map (MulAut.conj y).toMonoidHom ≤ V := fun y hy =>
    (le_iSup₂ (f := fun (y : G) (_ : y ∈ P) => Z2.map (MulAut.conj y).toMonoidHom) y hy)
  have hVQ : V ≤ Q := by
    apply dsConjClosure_le
    intro y hy
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    exact conj_mem_of_normalizer (hPQ hy) (hZ2S0 hz)
  have hVP : V ≤ P := hVQ.trans hQP
  have hPV : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V := by
    intro p hp v hv
    rw [← hVgen] at hv ⊢
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      apply Subgroup.subset_closure
      refine Set.mem_iUnion₂.mpr ⟨p * y, P.mul_mem hp hy, ?_⟩
      simp only [SetLike.mem_coe, mem_conj_map_iff] at hxy ⊢
      have e : (p * y)⁻¹ * (p * x * p⁻¹) * (p * y) = y⁻¹ * x * y := by group
      rw [e]; exact hxy
    | one => simp
    | mul x y _ _ ihx ihy =>
      have e : p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by group
      rw [e]; exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have e : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ ihx
  have hVnorm : P ≤ Subgroup.normalizer (V : Set G) := fun p hp => by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hPV p hp v hv, fun hv => ?_⟩
    have := hPV p⁻¹ (P.inv_mem hp) _ hv
    have e : p⁻¹ * (p * v * p⁻¹) * p⁻¹⁻¹ = v := by group
    rwa [e] at this
  have hcoreT : ∀ q ∈ Q, ∀ y ∈ P, ∀ z ∈ Z2, ⁅q, y * z * y⁻¹⁆ ∈ Z := by
    intro q hq y hy z hz
    have hq' : y⁻¹ * q * y ∈ Q := by
      have := conj_mem_of_normalizer (hPQ (P.inv_mem hy)) hq
      simpa using this
    have hc : ⁅z, y⁻¹ * q * y⁆ ∈ Z := hcore_S z hz _ (hQS' hq')
    have hc' : ⁅y⁻¹ * q * y, z⁆ ∈ Z := by
      rw [← commutatorElement_inv]; exact Z.inv_mem hc
    have e : ⁅q, y * z * y⁻¹⁆ = y * ⁅y⁻¹ * q * y, z⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_mem_of_normalizer (hPZ hy) hc'
  have hcoreV : ∀ q ∈ Q, ∀ e ∈ V, ⁅q, e⁆ ∈ Z := by
    intro q hq
    apply comm_with_normal_of_gen hVgen (N := Z)
    · intro x hx n hn
      exact conj_mem_of_normalizer (hPZ (hVP hx)) hn
    · intro a ha
      obtain ⟨y, hy, ha⟩ := Set.mem_iUnion₂.mp ha
      simp only [SetLike.mem_coe, mem_conj_map_iff] at ha
      have e : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
      rw [e]
      exact hcoreT q hq y hy _ ha
  have hnt : ∃ l ∈ L1, ∃ e ∈ V, ⁅l, e⁆ ∉ Z := by
    by_contra hcon
    push Not at hcon
    have key : ∀ l ∈ L1, ∀ z ∈ Z2, l * z * l⁻¹ ∈ Z2 := by
      intro l hl z hz
      have hc := hcon l hl z (hZ2V hz)
      have e : l * z * l⁻¹ = ⁅l, z⁆ * z := by simp only [commutatorElement_def]; group
      rw [e]
      exact Z2.mul_mem (hZZ2' hc) hz
    have hL1N : ∀ l ∈ L1, l ∈ Subgroup.normalizer (Z2 : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨key l hl z, fun hz => ?_⟩
      have := key l⁻¹ (L1.inv_mem hl) _ hz
      rwa [show l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z by group] at this
    have hPN : P ≤ Subgroup.normalizer (Z2 : Set G) := sup_le (fun l hl => hL1N l hl) hBN
    have hbot : Z2 = ⊥ := coreFree h.hyp.hyp (X := Z2) (isPGroup_of_isElemAbelian hZ2el)
      (hZ2S.trans le_sup_right) (fun l hl => hL1N l hl) (le_sup_left.trans hP2Z |>.trans le_rfl)
      (fun s hs => hBN s (hSB hs))
    exact hZ0' (le_bot_iff.mp (hZZ2'.trans (le_of_eq hbot)))
  have hbranch : ∃ x ∈ P, ¬ (Z2.map (MulAut.conj x).toMonoidHom ≤ R) := by
    by_contra hcon
    push Not at hcon
    have hVR : V ≤ R := dsConjClosure_le hcon
    have hTc : ∀ a ∈ (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)),
        ∀ b ∈ (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)),
          a * b = b * a := by
      intro a ha b hb
      obtain ⟨y, hy, ha⟩ := Set.mem_iUnion₂.mp ha
      obtain ⟨y', hy', hb⟩ := Set.mem_iUnion₂.mp hb
      simp only [SetLike.mem_coe, mem_conj_map_iff] at ha hb
      have hw : y⁻¹ * y' ∈ P := P.mul_mem (P.inv_mem hy) hy'
      have hb' : y⁻¹ * b * y ∈ R := by
        have hmem : y⁻¹ * b * y ∈ Z2.map (MulAut.conj (y⁻¹ * y')).toMonoidHom := by
          rw [mem_conj_map_iff]
          have e : (y⁻¹ * y')⁻¹ * (y⁻¹ * b * y) * (y⁻¹ * y') = y'⁻¹ * b * y' := by group
          rw [e]; exact hb
        exact hcon _ hw hmem
      have hc := hZ2R _ ha _ hb'
      calc a * b = y * ((y⁻¹ * a * y) * (y⁻¹ * b * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * b * y) * (y⁻¹ * a * y)) * y⁻¹ := by rw [← hc]
        _ = b * a := by group
    have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := comm_closure hVgen hTc
    have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
      intro v hv
      rw [← hVgen] at hv
      induction hv using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.mp hx
        simp only [SetLike.mem_coe, mem_conj_map_iff] at hx
        calc x ^ 2 = y * (y⁻¹ * x * y) ^ 2 * y⁻¹ := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [hZ2sq _ hx]; group
      | one => simp
      | mul x y hx hy ihx ihy =>
        have hxV : x ∈ V := hVgen ▸ hx
        have hyV : y ∈ V := hVgen ▸ hy
        have hxy : x * y = y * x := hVcomm x hxV y hyV
        have hxx : x * x = 1 := by rwa [pow_two] at ihx
        have hyy : y * y = 1 := by rwa [pow_two] at ihy
        rw [pow_two]
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hxx, hyy, one_mul]
      | inv x _ ihx => rw [inv_pow, ihx, inv_one]
    have hVel : IsElemAbelian 2 V :=
      ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2)), hV2⟩
    have hVcard : Nat.card V ≤ 16 := (rank_bounds (G := G)).2 V hVel
    have hZV : Z ≤ V := hZZ2'.trans hZ2V
    have hcomm0 : ⁅V, V⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hVcomm a ha b hb)]
      exact Z.one_mem
    have hsecV : IsElemSec Z V :=
      ⟨hZV, hcomm0, fun e he => by rw [hV2 e he]; exact Z.one_mem⟩
    have hcardZV : (Z.subgroupOf V).index ≤ 16 := by
      have h1 := Subgroup.card_mul_index (Z.subgroupOf V)
      have h2 : 0 < Nat.card ↥(Z.subgroupOf V) := Nat.card_pos
      nlinarith
    have hchief : A5Chief P L1 V Z :=
      faithful_a5 le_sup_left hPL1 hVP hVnorm hPZ hsecV hcardZV hq1 (fun q hq e he => hcoreV q hq e he) hnt
    have hc1 : (Z.subgroupOf V).index = 16 := hchief.card
    have h1 := Subgroup.card_mul_index (Z.subgroupOf V)
    have h2 : Nat.card ↥(Z.subgroupOf V) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
    have h3 : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZ0'
    rw [h2, hc1] at h1
    omega
  obtain ⟨x, hxP, hxR⟩ := hbranch
  have hBP2' : B ≤ L2 ⊔ B := le_sup_right
  have hxB : x ∉ B := by
    intro hxB
    apply hxR
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    exact hZ2R' (conj_mem_of_normalizer (hBN x hxB) hz)
  have hbr := bruhat h.hyp (Or.inl hq1)
  have hnotR : ∀ y ∈ P, y ∉ B → ¬ (Z2.map (MulAut.conj y).toMonoidHom ≤ R) := by
    intro y hy hyB hCR
    rcases hbr x hxP hxB y hy with hyB' | ⟨b1, hb1, b2, hb2, rfl⟩
    · exact hyB hyB'
    · apply hxR
      rw [Subgroup.map_le_iff_le_comap]
      intro z hz
      have hw : b2⁻¹ * z * b2 ∈ Z2 := by
        have hb2i : b2⁻¹ ∈ Subgroup.normalizer (Z2 : Set G) := hBN _ (B.inv_mem hb2)
        have := conj_mem_of_normalizer hb2i hz
        simpa using this
      have hmemC : (b1 * x * b2) * (b2⁻¹ * z * b2) * (b1 * x * b2)⁻¹ ∈
          Z2.map (MulAut.conj (b1 * x * b2)).toMonoidHom := by
        rw [mem_conj_map_iff]
        have e : (b1 * x * b2)⁻¹ * ((b1 * x * b2) * (b2⁻¹ * z * b2) * (b1 * x * b2)⁻¹) *
            (b1 * x * b2) = b2⁻¹ * z * b2 := by group
        rw [e]; exact hw
      have hR1 := hCR hmemC
      have e : b1 * (x * z * x⁻¹) * b1⁻¹ = (b1 * x * b2) * (b2⁻¹ * z * b2) * (b1 * x * b2)⁻¹ := by
        group
      have hR2 : b1 * (x * z * x⁻¹) * b1⁻¹ ∈ R := by rw [e]; exact hR1
      exact (Subgroup.mem_normalizer_iff.mp (hRN (hBP2' hb1)) (x * z * x⁻¹)).mpr hR2
  have hCsub : ∀ y ∈ P, Z2.map (MulAut.conj y).toMonoidHom ≤ Q := fun y hy =>
    (hCV y hy).trans hVQ
  have hQC : ∀ y ∈ P, ∀ q ∈ Q, ∀ c ∈ Z2.map (MulAut.conj y).toMonoidHom,
      q * c * q⁻¹ ∈ Z2.map (MulAut.conj y).toMonoidHom := by
    intro y hy q hq c hc
    have hq' : y⁻¹ * q * y ∈ Q := by
      have := conj_mem_of_normalizer (hPQ (P.inv_mem hy)) hq
      simpa using this
    have hq'N : y⁻¹ * q * y ∈ Subgroup.normalizer (Z2 : Set G) :=
      hP2Z (hSP2 (hQS' hq'))
    rw [mem_conj_map_iff] at hc ⊢
    have := conj_mem_of_normalizer hq'N hc
    have e : y⁻¹ * (q * c * q⁻¹) * y = (y⁻¹ * q * y) * (y⁻¹ * c * y) * (y⁻¹ * q * y)⁻¹ := by
      group
    rw [e]; exact this
  have hint : ∀ y ∈ P, y ∉ B → ∀ a ∈ Z2, a ∈ Z2.map (MulAut.conj y).toMonoidHom → a ∈ Z := by
    intro y hy hyB a ha haC
    obtain ⟨z', hz'C, hz'R⟩ := exists_not_mem_of_not_le (hnotR y hy hyB)
    have hz'S : z' ∈ S := hQS' (hCsub y hy hz'C)
    have hcomm' : z' * a = a * z' :=
      (conj_comm hZ2el y haC hz'C).symm
    exact core_of_comm_outside hRS hRi' hZ2R hZch hZ2sq hZ2S a ha z' hz'S hz'R hcomm'
  have hpair : ∀ y ∈ P, ∀ a ∈ Z2, ∀ c ∈ Z2.map (MulAut.conj y).toMonoidHom, ⁅a, c⁆ ∈ Z := by
    intro y hy a ha c hc
    by_cases hyB : y ∈ B
    · have hcZ2 : c ∈ Z2 := by
        rw [mem_conj_map_iff] at hc
        have := conj_mem_of_normalizer (hBN y hyB) hc
        have e : y * (y⁻¹ * c * y) * y⁻¹ = c := by group
        rw [e] at this
        exact this
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (comm_of_isElemAbelian hZ2el ha hcZ2)]
      exact Z.one_mem
    · have hcQ : c ∈ Q := hCsub y hy hc
      have h1 : ⁅a, c⁆ ∈ Z2 := by
        have hcn : c * a⁻¹ * c⁻¹ ∈ Z2 :=
          conj_mem_of_normalizer (hP2Z (hSP2 (hQS' hcQ))) (Z2.inv_mem ha)
        have e : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact Z2.mul_mem ha hcn
      have h2 : ⁅a, c⁆ ∈ Z2.map (MulAut.conj y).toMonoidHom := by
        have hac := hQC y hy a (hZ2S0 ha) c hc
        have e : ⁅a, c⁆ = (a * c * a⁻¹) * c⁻¹ := by
          simp only [commutatorElement_def, mul_assoc]
        rw [e]
        exact Subgroup.mul_mem _ hac (Subgroup.inv_mem _ hc)
      exact hint y hy hyB ⁅a, c⁆ h1 h2
  have hsqC : ∀ y ∈ P, ∀ a ∈ Z2.map (MulAut.conj y).toMonoidHom, a ^ 2 = 1 := by
    intro y hy a ha
    rw [mem_conj_map_iff] at ha
    calc a ^ 2 = y * (y⁻¹ * a * y) ^ 2 * y⁻¹ := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hZ2sq _ ha]; group
  have hTcomm : ∀ a ∈ (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)),
      ∀ b ∈ (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)),
        ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    obtain ⟨y, hy, ha⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨y', hy', hb⟩ := Set.mem_iUnion₂.mp hb
    simp only [SetLike.mem_coe, mem_conj_map_iff] at ha hb
    have hw : y⁻¹ * y' ∈ P := P.mul_mem (P.inv_mem hy) hy'
    have hb' : y⁻¹ * b * y ∈ Z2.map (MulAut.conj (y⁻¹ * y')).toMonoidHom := by
      rw [mem_conj_map_iff]
      have e : (y⁻¹ * y')⁻¹ * (y⁻¹ * b * y) * (y⁻¹ * y') = y'⁻¹ * b * y' := by group
      rw [e]; exact hb
    have hp := hpair (y⁻¹ * y') hw (y⁻¹ * a * y) ha (y⁻¹ * b * y) hb'
    have e : ⁅a, b⁆ = y * ⁅y⁻¹ * a * y, y⁻¹ * b * y⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact conj_mem_of_normalizer (hPZ hy) hp
  have hZsubC : ∀ y ∈ P, Z ≤ Z2.map (MulAut.conj y).toMonoidHom := by
    intro y hy c hc
    rw [mem_conj_map_iff]
    have := conj_mem_of_normalizer (hPZ (P.inv_mem hy)) hc
    have h2 : y⁻¹ * c * y ∈ Z := by simpa using this
    exact hZZ2' h2
  have hZcentV : ∀ c ∈ Z, ∀ x ∈ V, c * x = x * c := by
    intro c hc
    refine central_of_gen hVgen (z := c) ?_
    intro t ht
    obtain ⟨y, hy, ht⟩ := Set.mem_iUnion₂.mp ht
    exact conj_comm hZ2el y (hZsubC y hy hc) ht
  have hcommVV : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z := comm_mem_of_gen hVgen hZcentV hTcomm
  have hsqT : ∀ a ∈ (⋃ y ∈ P, ((Z2.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)),
      a ^ 2 ∈ Z := by
    intro a ha
    obtain ⟨y, hy, ha⟩ := Set.mem_iUnion₂.mp ha
    rw [hsqC y hy a ha]
    exact Z.one_mem
  have hsqV : ∀ a ∈ V, a ^ 2 ∈ Z := sq_mem_of_gen hVgen hZcentV hcommVV hsqT
  have hZV : Z ≤ V := hZZ2'.trans hZ2V
  have hsecV : IsElemSec Z V := ⟨hZV, Subgroup.commutator_le.mpr hcommVV, hsqV⟩
  have hVp2 : IsPGroup 2 V := by
    have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
    exact isPGroup_of_le_of hQ2 hVQ
  have hfr : dsFrattini V ≤ Z := dsFrattini_le_of_comm_sq hVp2
    (Subgroup.commutator_le.mpr hcommVV) hsqV
  have hZrel : Z.relIndex V ≤ 16 := by
    have h1 := (rank_bounds (G := G)).1 V hVp2
    have h2 : (dsFrattini V).relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Subgroup.relIndex_le_of_le_left hfr h2).trans h1
  have hchief : A5Chief P L1 V Z :=
    faithful_a5 le_sup_left hPL1 hVP hVnorm hPZ hsecV hZrel hq1
      (fun q hq e he => hcoreV q hq e he) hnt
  obtain ⟨w, hwC, hwR⟩ := exists_not_mem_of_not_le hxR
  have hwS : w ∈ S := hQS' (hCsub x hxP hwC)
  have hwV : w ∈ V := hCV x hxP hwC
  have hZ2card' : Nat.card Z2 = Nat.card Z ^ 2 := hJ2c
  have hZ4 : Nat.card Z ≠ 4 := by
    intro hZ4
    have hZ2c16 : Nat.card Z2 = 16 := by rw [hZ2card', hZ4]; norm_num
    classical
    haveI : Fintype G := Fintype.ofFinite G
    have hPB : ¬ P ≤ B := fun hle => hxB (hle hxP)
    have hI5 : (borelOf L1 S).relIndex L1 = 5 := borel_index_five h hQL1 hPB
    let H' : Subgroup ↥L1 := (borelOf L1 S).subgroupOf L1
    have hcardQ : Nat.card (↥L1 ⧸ H') = 5 := hI5
    let e : (↥L1 ⧸ H') ≃ Fin 5 := (Finite.equivFin _).trans (finCongr hcardQ)
    let rep : Fin 5 → ↥L1 := fun i => (e.symm i).out
    have hrep : ∀ i, (QuotientGroup.mk (rep i) : ↥L1 ⧸ H') = e.symm i :=
      fun i => Quotient.out_eq _
    have hL1P : L1 ≤ P := le_sup_left
    have hrepP : ∀ i, (rep i : G) ∈ P := fun i => hL1P (rep i).2
    let A : Fin 5 → Subgroup G := fun i => Z2.map (MulAut.conj (rep i : G)).toMonoidHom
    have hAV : ∀ i, A i ≤ V := fun i => hCV _ (hrepP i)
    have hAcard : ∀ i, Nat.card (A i) = 16 := by
      intro i
      rw [← hZ2c16]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj (rep i : G)).toMonoidHom)
        (MulAut.conj (rep i : G)).injective
    have hAZ : ∀ i, Z ≤ A i := fun i => hZsubC _ (hrepP i)
    have hAsq : ∀ i, ∀ a ∈ A i, a ^ 2 = 1 := fun i a ha => hsqC _ (hrepP i) a ha
    have hAint : ∀ i j, i ≠ j → ∀ a ∈ A i, a ∈ A j → a ∈ Z := by
      intro i j hij a hai haj
      have hyB : (rep i : G)⁻¹ * (rep j : G) ∉ B := by
        intro hyB
        have hyL1 : (rep i : G)⁻¹ * (rep j : G) ∈ L1 :=
          L1.mul_mem (L1.inv_mem (rep i).2) (rep j).2
        have hyH : (rep i : G)⁻¹ * (rep j : G) ∈ borelOf L1 S := by
          rw [← F1.inf_bigB_eq_borelOf h.hyp]
          exact ⟨hyL1, hyB⟩
        have hmemH : ((rep i)⁻¹ * rep j : ↥L1) ∈ H' := Subgroup.mem_subgroupOf.mpr hyH
        have hq : (QuotientGroup.mk (rep i) : ↥L1 ⧸ H') = QuotientGroup.mk (rep j) :=
          (QuotientGroup.eq).mpr hmemH
        rw [hrep, hrep] at hq
        exact hij (e.symm.injective hq)
      have hyP : (rep i : G)⁻¹ * (rep j : G) ∈ P :=
        P.mul_mem (P.inv_mem (hrepP i)) (hrepP j)
      have hai' := hai
      have haj' := haj
      rw [mem_conj_map_iff] at hai' haj'
      have hu : (rep i : G)⁻¹ * a * (rep i : G) ∈ Z2 := hai'
      have huC : (rep i : G)⁻¹ * a * (rep i : G) ∈ Z2.map (MulAut.conj ((rep i : G)⁻¹ * (rep j : G))).toMonoidHom := by
        rw [mem_conj_map_iff]
        have e1 : ((rep i : G)⁻¹ * (rep j : G))⁻¹ * ((rep i : G)⁻¹ * a * (rep i : G)) *
            ((rep i : G)⁻¹ * (rep j : G)) = (rep j : G)⁻¹ * a * (rep j : G) := by group
        rw [e1]; exact haj'
      have hu' := hint _ hyP hyB _ hu huC
      have ha' : a = (rep i : G) * ((rep i : G)⁻¹ * a * (rep i : G)) * (rep i : G)⁻¹ := by group
      rw [ha']
      exact conj_mem_of_normalizer (hPZ (hrepP i)) hu'
    let D : Fin 5 → Finset G := fun i =>
      (Finset.univ.filter (fun g => g ∈ A i)) \ (Finset.univ.filter (fun g => g ∈ Z))
    have hcardFilt : ∀ T : Subgroup G, Nat.card T = (Finset.univ.filter (fun g => g ∈ T)).card := by
      intro T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hDcard : ∀ i, (D i).card = 12 := by
      intro i
      have hsub : Finset.univ.filter (fun g => g ∈ Z) ⊆ Finset.univ.filter (fun g => g ∈ A i) := by
        intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        exact hAZ i hg
      rw [Finset.card_sdiff_of_subset hsub]
      rw [← hcardFilt, ← hcardFilt, hAcard i, hZ4]
    have hDdisj : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)),
        i ≠ j → Disjoint (D i) (D j) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro g hgi hgj
      simp only [D, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hgi hgj
      exact hgi.2 (hAint i j hij g hgi.1 hgj.1)
    let U : Finset G := Finset.univ.biUnion D
    have hUcard : U.card = 60 := by
      rw [Finset.card_biUnion hDdisj]
      simp [hDcard]
    have hWcard : (Finset.univ.filter (fun g => g ∈ V) \ Finset.univ.filter (fun g => g ∈ Z)).card ≤ 60 := by
      have hsub : Finset.univ.filter (fun g => g ∈ Z) ⊆ Finset.univ.filter (fun g => g ∈ V) := by
        intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        exact hZV hg
      rw [Finset.card_sdiff_of_subset hsub, ← hcardFilt, ← hcardFilt, hZ4]
      have hV64 : Nat.card V ≤ 64 := by
        have h1 := Subgroup.card_mul_index (Z.subgroupOf V)
        have h2 : Nat.card ↥(Z.subgroupOf V) = Nat.card Z :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
        have h3 : (Z.subgroupOf V).index ≤ 16 := hZrel
        rw [h2, hZ4] at h1
        nlinarith
      omega
    have hUsub : U ⊆ Finset.univ.filter (fun g => g ∈ V) \ Finset.univ.filter (fun g => g ∈ Z) := by
      intro g hg
      simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] at hg
      obtain ⟨i, hi⟩ := hg
      simp only [D, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hAV i hi.1, hi.2⟩
    have hUeq := Finset.eq_of_subset_of_card_le hUsub (by omega)
    have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
      intro v hv
      by_cases hvZ : v ∈ Z
      · exact hAsq 0 v (hAZ 0 hvZ)
      · have hvU : v ∈ U := by
          rw [hUeq]
          simp [hv, hvZ]
        simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] at hvU
        obtain ⟨i, hi⟩ := hvU
        simp only [D, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hAsq i v hi.1
    have hcomm_w : ∀ z ∈ Z2, w * z = z * w := by
      intro z hz
      have hzw : (z * w) * (z * w) = 1 := by
        rw [← pow_two]; exact hVexp _ (V.mul_mem (hZ2V hz) hwV)
      have hzz : z * z = 1 := by rw [← pow_two]; exact hZ2sq z hz
      have hww : w * w = 1 := by rw [← pow_two]; exact hVexp w hwV
      have hinv := mul_eq_one_iff_eq_inv.mp hzw
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hww] at hinv
      exact hinv.symm
    have hZ2Z : Z2 ≤ Z := fun z hz =>
      core_of_comm_outside hRS hRi' hZ2R hZch hZ2sq hZ2S z hz w hwS hwR
        (hcomm_w z hz) 
    have := Subgroup.card_le_of_le hZ2Z
    rw [hZ2card', hZ4] at this
    norm_num at this
  have hZcard : Nat.card Z = 2 := by
    have hZp : IsPGroup 2 Z := isPGroup_of_le_of (isPGroup_of_isElemAbelian hZ2el) hZZ2'
    obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).mp hZp
    have hle4 : Nat.card Z ≤ 4 := hJ2d
    have hgt : 1 < Nat.card Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZ0'
    have h3 : Nat.card Z ≠ 3 := fun h3 => by
      have h32 : 3 ∣ 2 ^ n := h3 ▸ hn
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
    omega
  have hZ2nonc : ∃ a ∈ Z2, ⁅a, w⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hZ2Z : Z2 ≤ Z := fun a ha =>
      core_of_comm_outside hRS hRi' hZ2R hZch hZ2sq hZ2S a ha w hwS hwR
        (commutatorElement_eq_one_iff_mul_comm.mp (hcon a ha)).symm
    have hle := Subgroup.card_le_of_le hZ2Z
    rw [hZ2card', hZcard] at hle
    norm_num at hle
  have hNatSec : ¬ NatSec L1 Z V := by
    intro hN
    obtain ⟨⟨d, hdB, hd3⟩, -⟩ := DSBA5.three_and_card h.hyp.hyp.h1.sylow hq1
    have hdL : d ∈ L1 := F1.borelOf_le L1 S hdB
    obtain ⟨z, hz, hzZ⟩ : ∃ z ∈ Z2, z ∉ Z := by
      by_contra hc
      push Not at hc
      have hle := Subgroup.card_le_of_le (show Z2 ≤ Z from hc)
      rw [hZ2card', hZcard] at hle
      norm_num at hle
    have hdz : d * z = z * d := commutatorElement_eq_one_iff_mul_comm.mp (hJ2e d hdB hd3 z hz)
    have hzd : ⁅z, d⁆ ∈ Z := by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hdz.symm]
      exact Z.one_mem
    exact hzZ (hN d hdL hd3 z (hZ2V hz) hzd)
  have hVZ : ⁅V, V⁆ = Z := by
    have hle : ⁅V, V⁆ ≤ Z := Subgroup.commutator_le.mpr hcommVV
    obtain ⟨a, haZ2, ha⟩ := hZ2nonc
    have hne : ⁅V, V⁆ ≠ ⊥ := by
      intro hbot
      apply ha
      have hmem : ⁅a, w⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator (hZ2V haZ2) hwV
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have h1 : 1 < Nat.card ↥(⁅V, V⁆ : Subgroup G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hZcard]
    omega
  exact ⟨hZcard, hchief, hNatSec, hVZ, hVQ⟩

end DSBJV1

theorem leafDSBJV1 [DSLeaf LeafDSBJZ2] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafZiStructure] [DSLeaf LeafChiefOfA5] [DSLeaf LeafM3] [DSLeaf LeafM5] [DSLeaf LeafBruhat] [DSLeaf LeafRankBounds] [DSLeaf LeafSylowS] [DSLeaf LeafFaithfulA5] : LeafDSBJV1 := by
  intro G _ _ L1 L2 S h cJ
  exact DSBJV1.main_V h cJ

end CFSG.GH74.QTGen4.DSGen4
