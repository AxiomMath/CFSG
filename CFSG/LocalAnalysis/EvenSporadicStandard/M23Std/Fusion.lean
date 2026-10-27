module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.HomReduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.SylowFusion

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

structure FusionData (L : Subgroup G) (t : G) (T1 F1 F2 : Subgroup G) (m : G) : Prop where
  T1_le : T1 ≤ L
  T1_pgroup : IsPGroup 2 T1
  T1_odd : ¬ 2 ∣ T1.relIndex L
  t_mem : t ∈ T1
  t_central : ∀ x ∈ T1, t * x = x * t
  T1_center : ∀ x ∈ T1, (∀ y ∈ T1, x * y = y * x) → x = 1 ∨ x = t
  T1_gen : Subgroup.closure {a : G | a ∈ T1 ∧ a * a = 1} = T1
  F1_le : F1 ≤ T1
  F2_le : F2 ≤ T1
  F1_comm : ∀ x ∈ F1, ∀ y ∈ F1, x * y = y * x
  F2_comm : ∀ x ∈ F2, ∀ y ∈ F2, x * y = y * x
  F1_sq : ∀ x ∈ F1, x * x = 1
  F2_sq : ∀ x ∈ F2, x * x = 1
  F1_card : Nat.card F1 = 16
  F2_card : Nat.card F2 = 16
  F_ne : F1 ≠ F2
  F_only : ∀ F : Subgroup G, F ≤ T1 → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x * x = 1) →
    Nat.card F = 16 → F = F1 ∨ F = F2
  t_mem_F1 : t ∈ F1
  t_mem_F2 : t ∈ F2
  m_mem : m ∈ L
  m_F1 : ∀ x, x ∈ F1 ↔ m * x * m⁻¹ ∈ F1
  m_F2 : ∀ x, x ∈ F2 ↔ m * x * m⁻¹ ∈ F2
  m_t : m * t * m⁻¹ ≠ t

section Basic

variable {L : Subgroup G} {z t : G}

theorem mem_zpowers_involution {z : G} (hz : z * z = 1) {b : G} (hb : b ∈ zpowers z) :
    b = 1 ∨ b = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  have : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    rw [show z ^ (2 : ℤ) = 1 by exact_mod_cast hz2, one_zpow, mul_one]
  rw [this]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> simp [h0]

end Basic

section Main

variable {L : Subgroup G} {z t : G} {T1 F1 F2 : Subgroup G} {m : G}

theorem zpowers_le_centralizer_of_le (h : OneClassData L z t) {S : Subgroup G} (hS : S ≤ L) :
    zpowers z ≤ centralizer (S : Set G) := by
  rw [Subgroup.zpowers_le]
  exact mem_centralizer_iff.2 fun a ha => (h.z_comm a (hS ha)).symm

theorem centralizer_z_eq (h : OneClassData L z t) :
    centralizer ({z} : Set G) = L ⊔ zpowers z := by
  apply le_antisymm
  · intro g hg
    have hg' : z * g = g * z := (mem_centralizer_singleton_iff.1 hg).symm
    obtain ⟨l, hl, hcases⟩ := h.centralizer_z g hg'
    rcases hcases with rfl | rfl
    · exact Subgroup.mem_sup_left hl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  · refine sup_le (fun l hl => ?_) ?_
    · exact mem_centralizer_singleton_iff.2 (h.z_comm l hl).symm
    · rw [Subgroup.zpowers_le]
      exact mem_centralizer_singleton_iff.2 rfl

theorem disjoint_zpowers (h : OneClassData L z t) {S : Subgroup G} (hS : S ≤ L) :
    Disjoint S (zpowers z) := by
  rw [Subgroup.disjoint_def]
  intro x hxS hxz
  rcases mem_zpowers_involution h.z_mul_self hxz with rfl | rfl
  · rfl
  · exact absurd (hS hxS) h.z_not_mem

theorem card_zpowers_z (h : OneClassData L z t) : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact h.z_mul_self) h.z_ne_one

theorem card_sup_zpowers (h : OneClassData L z t) {S : Subgroup G} (hS : S ≤ L) :
    Nat.card (S ⊔ zpowers z : Subgroup G) = Nat.card S * 2 := by
  have e := mulEquivProdSup (A := S) (B := zpowers z)
    (zpowers_le_centralizer_of_le h hS) (disjoint_zpowers h hS)
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, card_zpowers_z h]

theorem sylow_T [Finite G] (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) :
    (T1 ⊔ zpowers z) ≤ centralizer ({z} : Set G) ∧ IsPGroup 2 (T1 ⊔ zpowers z : Subgroup G) ∧
      ¬ 2 ∣ (T1 ⊔ zpowers z : Subgroup G).relIndex (centralizer ({z} : Set G)) := by
  have hC := centralizer_z_eq h
  have hle : T1 ⊔ zpowers z ≤ L ⊔ zpowers z := sup_le_sup_right D.T1_le _
  refine ⟨hC ▸ hle, ?_, ?_⟩
  · have hnorm : T1 ≤ normalizer (zpowers z : Set G) := by
      intro a ha
      apply Subgroup.centralizer_le_normalizer
      refine mem_centralizer_iff.2 fun b hb => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_left (h.z_comm a (D.T1_le ha)) k).eq
    refine D.T1_pgroup.to_sup_of_normal_right' (IsPGroup.of_card (n := 1) ?_) hnorm
    rw [card_zpowers_z h]; rfl
  · rw [hC]
    have h1 := Subgroup.relIndex_mul_card (T1 ⊔ zpowers z) (L ⊔ zpowers z)
    rw [inf_eq_left.mpr hle, card_sup_zpowers h D.T1_le] at h1
    have h2 := Subgroup.relIndex_mul_card T1 L
    rw [inf_eq_left.mpr D.T1_le] at h2
    have hc : Nat.card (L ⊔ zpowers z : Subgroup G) = Nat.card L * 2 := card_sup_zpowers h le_rfl
    have hpos : 0 < Nat.card T1 := Nat.card_pos
    have : (T1 ⊔ zpowers z).relIndex (L ⊔ zpowers z) = T1.relIndex L := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos (by norm_num : 0 < 2))
      rw [h1, hc, ← h2]
      ring
    rw [this]
    exact D.T1_odd

theorem fused_all [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : OneClassData L z t) {u : G} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    IsConj z (u * z) := by
  obtain ⟨l, hl, hl2, hl1, hconj⟩ := h.exists_fused hnonab
  exact h.isConj_mul_z hl hl2 hl1 hconj hu hu2 hu1

theorem exists_n [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) :
    ∃ n : G, (∀ x, x ∈ T1 ⊔ zpowers z ↔ n * x * n⁻¹ ∈ T1 ⊔ zpowers z) ∧
      n * z * n⁻¹ = z * t := by
  have hconj : IsConj z (z * t) := by
    rw [h.z_comm t h.t_mem]
    exact fused_all hnonab h h.t_mem h.t_mul_self h.t_ne_one
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  refine exists_mem_normalizer_conj_eq (sylow_T h D) hg ?_
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.T1_le) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hzt : Commute z t := h.z_comm t h.t_mem
  have haz : Commute a z := (h.z_comm a (D.T1_le ha)).symm
  have hat : Commute a t := (D.t_central a ha).symm
  have hbz : Commute (z ^ k) z := (Commute.refl z).zpow_left k
  have hbt : Commute (z ^ k) t := hzt.zpow_left k
  exact (((haz.mul_right hat).mul_left (hbz.mul_right hbt))).eq

theorem t_central_T (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) {x : G}
    (hx : x ∈ T1 ⊔ zpowers z) : t * x = x * t := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.T1_le) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hzt : Commute z t := h.z_comm t h.t_mem
  have hat : Commute t a := D.t_central a ha
  have hbt : Commute t (z ^ k) := (hzt.zpow_left k).symm
  exact (hat.mul_right hbt).eq

theorem n_conj_t [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) {n : G}
    (hn : ∀ x, x ∈ T1 ⊔ zpowers z ↔ n * x * n⁻¹ ∈ T1 ⊔ zpowers z) :
    n * t * n⁻¹ = t := by
  have htT : t ∈ T1 ⊔ zpowers z := Subgroup.mem_sup_left D.t_mem
  have hyT : n * t * n⁻¹ ∈ T1 ⊔ zpowers z := (hn t).1 htT
  have hycent : ∀ u ∈ T1 ⊔ zpowers z, (n * t * n⁻¹) * u = u * (n * t * n⁻¹) := by
    intro u hu
    have hw : n⁻¹ * u * n ∈ T1 ⊔ zpowers z := by
      refine (hn (n⁻¹ * u * n)).2 ?_
      have : n * (n⁻¹ * u * n) * n⁻¹ = u := by group
      rwa [this]
    have h1 := t_central_T h D hw
    calc n * t * n⁻¹ * u = n * (t * (n⁻¹ * u * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * u * n) * t) * n⁻¹ := by rw [h1]
      _ = u * (n * t * n⁻¹) := by group
  obtain ⟨a, ha, b, hb, hy⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.T1_le) hyT
  have hbc : ∀ u ∈ T1, b * u = u * b := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_left (h.z_comm u (D.T1_le hu)) k).eq
  have hacomm : ∀ u ∈ T1, a * u = u * a := by
    intro u hu
    have h1 := hycent u (Subgroup.mem_sup_left hu)
    rw [hy] at h1
    have h2 : a * (b * u) = u * a * b := by
      calc a * (b * u) = a * b * u := by rw [mul_assoc]
        _ = u * (a * b) := h1
        _ = u * a * b := by rw [mul_assoc]
    rw [hbc u hu, ← mul_assoc] at h2
    exact mul_right_cancel h2
  have ht1 := h.t_ne_one
  rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
  · rcases D.T1_center a ha hacomm with ha1 | hat
    · exfalso
      rw [hb1, ha1, one_mul] at hy
      exact ht1 (conj_eq_one_iff.1 hy)
    · rw [hb1, hat, mul_one] at hy
      exact hy
  · exfalso
    rcases D.T1_center a ha hacomm with ha1 | hat
    · rw [hbz, ha1, one_mul] at hy
      apply h.not_isConj_z_t
      exact isConj_iff.2 ⟨n⁻¹, by rw [← hy]; group⟩
    · rw [hbz, hat] at hy
      apply h.not_isConj_z_t
      have h1 : IsConj z (t * z) := fused_all hnonab h h.t_mem h.t_mul_self ht1
      have h2 : IsConj t (t * z) := by rw [← hy]; exact isConj_iff.2 ⟨n, rfl⟩
      exact h1.trans h2.symm

theorem conj_involution_mem_T1 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) {n : G}
    (hn : ∀ x, x ∈ T1 ⊔ zpowers z ↔ n * x * n⁻¹ ∈ T1 ⊔ zpowers z) {a : G} (ha : a ∈ T1)
    (ha2 : a * a = 1) : n * a * n⁻¹ ∈ T1 := by
  by_cases ha1 : a = 1
  · subst ha1
    simp
  have hyT : n * a * n⁻¹ ∈ T1 ⊔ zpowers z := (hn a).1 (Subgroup.mem_sup_left ha)
  obtain ⟨b, hb, c, hc, hy⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.T1_le) hyT
  have hy2 : (n * a * n⁻¹) * (n * a * n⁻¹) = 1 := by
    calc (n * a * n⁻¹) * (n * a * n⁻¹) = n * (a * a) * n⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  rcases mem_zpowers_involution h.z_mul_self hc with hc1 | hcz
  · rw [hy, hc1, mul_one]
    exact hb
  · exfalso
    have hbz : b * z = z * b := (h.z_comm b (D.T1_le hb)).symm
    have hb2 : b * b = 1 := by
      rw [hy, hcz] at hy2
      calc b * b = b * b * (z * z) := by rw [h.z_mul_self, mul_one]
        _ = b * z * (b * z) := by
          calc b * b * (z * z) = b * (b * z) * z := by simp only [mul_assoc]
            _ = b * (z * b) * z := by rw [hbz]
            _ = b * z * (b * z) := by
              calc b * (z * b) * z = b * z * b * z := by simp only [mul_assoc]
                _ = b * z * (b * z) := by simp only [mul_assoc]
        _ = 1 := hy2
    have hconj : IsConj a (n * a * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
    by_cases hb1 : b = 1
    · rw [hy, hcz, hb1, one_mul] at hconj
      exact h.not_isConj_z_of_mem (D.T1_le ha) ha2 ha1 hconj.symm
    · have h1 : IsConj z (b * z) := fused_all hnonab h (D.T1_le hb) hb2 hb1
      rw [hy, hcz] at hconj
      exact h.not_isConj_z_of_mem (D.T1_le ha) ha2 ha1 (h1.trans hconj.symm)

theorem normalizes_T1 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : OneClassData L z t) (D : FusionData L t T1 F1 F2 m) {n : G}
    (hn : ∀ x, x ∈ T1 ⊔ zpowers z ↔ n * x * n⁻¹ ∈ T1 ⊔ zpowers z) :
    ∀ x, x ∈ T1 ↔ n * x * n⁻¹ ∈ T1 := by
  have hn' : ∀ x, x ∈ T1 ⊔ zpowers z ↔ n⁻¹ * x * n⁻¹⁻¹ ∈ T1 ⊔ zpowers z := by
    intro x
    have := hn (n⁻¹ * x * n⁻¹⁻¹)
    rw [show n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ = x by group] at this
    exact this.symm
  have key : ∀ {k : G}, (∀ x, x ∈ T1 ⊔ zpowers z ↔ k * x * k⁻¹ ∈ T1 ⊔ zpowers z) →
      ∀ x ∈ T1, k * x * k⁻¹ ∈ T1 := by
    intro k hk x hx
    have : x ∈ T1.comap (MulAut.conj k).toMonoidHom := by
      rw [← D.T1_gen] at hx
      refine (Subgroup.closure_le (T1.comap (MulAut.conj k).toMonoidHom)).2 ?_ hx
      rintro a ⟨ha, ha2⟩
      exact conj_involution_mem_T1 hnonab h D hk ha ha2
    exact this
  intro x
  refine ⟨key hn x, fun hx => ?_⟩
  have := key hn' _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

def cj (n : G) (F : Subgroup G) : Subgroup G := F.comap (MulAut.conj n).toMonoidHom

theorem mem_cj {n : G} {F : Subgroup G} {x : G} : x ∈ cj n F ↔ n * x * n⁻¹ ∈ F := Iff.rfl

theorem card_cj [Finite G] (n : G) (F : Subgroup G) : Nat.card (cj n F) = Nat.card F :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj n).toEquiv (fun _ => Iff.rfl))

theorem cj_eq_or [Finite G] (D : FusionData L t T1 F1 F2 m) {n : G}
    (hn : ∀ x, x ∈ T1 ↔ n * x * n⁻¹ ∈ T1) {F : Subgroup G} (hF : F ≤ T1)
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1) (hcard : Nat.card F = 16) :
    cj n F = F1 ∨ cj n F = F2 := by
  refine D.F_only (cj n F) (fun x hx => (hn x).2 (hF (mem_cj.1 hx))) ?_ ?_
    (by rw [card_cj, hcard])
  · intro x hx y hy
    have e : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
      calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * y * n⁻¹) * (n * x * n⁻¹) := hc _ (mem_cj.1 hx) _ (mem_cj.1 hy)
        _ = n * (y * x) * n⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  · intro x hx
    have e : n * (x * x) * n⁻¹ = 1 := by
      calc n * (x * x) * n⁻¹ = (n * x * n⁻¹) * (n * x * n⁻¹) := by group
        _ = 1 := hs _ (mem_cj.1 hx)
    exact conj_eq_one_iff.1 e

theorem forall_mem_iff_of_forall_mem [Finite G] {E : Subgroup G} {c : G}
    (hc : ∀ x ∈ E, c * x * c⁻¹ ∈ E) : ∀ x, x ∈ E ↔ c * x * c⁻¹ ∈ E := by
  intro x
  refine ⟨hc x, fun hx => ?_⟩
  let f : E → E := fun y => ⟨c * y * c⁻¹, hc y y.2⟩
  have hinj : Function.Injective f := by
    intro y y' hyy
    have : c * (y : G) * c⁻¹ = c * (y' : G) * c⁻¹ := congrArg Subtype.val hyy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨c * x * c⁻¹, hx⟩
  have : c * (y : G) * c⁻¹ = c * x * c⁻¹ := congrArg Subtype.val hy
  have hyx : (y : G) = x := mul_left_cancel (mul_right_cancel this)
  rw [← hyx]
  exact y.2

theorem mem_normalizer_sup [Finite G] (h : OneClassData L z t) {F : Subgroup G} (hFL : F ≤ L)
    {c s : G} (hcF : ∀ x, x ∈ F ↔ c * x * c⁻¹ ∈ F) (hs : s ∈ F) (hcz : c * z * c⁻¹ = z * s) :
    ∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z := by
  apply forall_mem_iff_of_forall_mem
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h hFL) hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : c * (a * z ^ k) * c⁻¹ = (c * a * c⁻¹) * (z * s) ^ k := by
    rw [← hcz, conj_zpow]
    group
  rw [h1]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hcF a).1 ha)) ?_
  refine Subgroup.zpow_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left hs)) k
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem exists_normalizer_moving_z [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h : OneClassData L z t)
    (D : FusionData L t T1 F1 F2 m) :
    ∃ c : G, (∀ x, x ∈ F1 ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F1 ⊔ zpowers z) ∧
      ∃ s ∈ F1, s ≠ 1 ∧ c * z * c⁻¹ = z * s := by
  obtain ⟨n, hn, hnz⟩ := exists_n hnonab h D
  have hnt := n_conj_t hnonab h D hn
  have hnT1 := normalizes_T1 hnonab h D hn
  have hF1L : F1 ≤ L := D.F1_le.trans D.T1_le
  have hcases1 := cj_eq_or D hnT1 D.F1_le D.F1_comm D.F1_sq D.F1_card
  have hcases2 := cj_eq_or D hnT1 D.F2_le D.F2_comm D.F2_sq D.F2_card
  rcases hcases1 with hA | hB
  · have hnF1 : ∀ x, x ∈ F1 ↔ n * x * n⁻¹ ∈ F1 := fun x => by rw [← mem_cj, hA]
    exact ⟨n, mem_normalizer_sup h hF1L hnF1 D.t_mem_F1 hnz, t, D.t_mem_F1, h.t_ne_one, hnz⟩
  · have hB1 : ∀ x, x ∈ F2 ↔ n * x * n⁻¹ ∈ F1 := fun x => by rw [← mem_cj, hB]
    have hB2 : ∀ x, x ∈ F1 ↔ n * x * n⁻¹ ∈ F2 := by
      rcases hcases2 with hC | hC
      · intro x
        rw [← mem_cj, hC]
      · exfalso
        apply D.F_ne
        ext y
        have := Subgroup.ext_iff.1 (hB.trans hC.symm) (n⁻¹ * y * n)
        rwa [mem_cj, mem_cj, show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at this
    set c : G := n * m * n⁻¹ * m⁻¹ with hc
    have hmz : m * z * m⁻¹ = z := by
      rw [← h.z_comm m D.m_mem]
      group
    have hmz' : m⁻¹ * z * m = z := by
      have := h.z_comm m⁻¹ (Subgroup.inv_mem _ D.m_mem)
      rw [← this]
      group
    have hz' : z = n * (z * t) * n⁻¹ := by
      calc z = z * t * t := by rw [mul_assoc, h.t_mul_self, mul_one]
        _ = (n * z * n⁻¹) * (n * t * n⁻¹) := by rw [hnz, hnt]
        _ = n * (z * t) * n⁻¹ := by group
    have hnz' : n⁻¹ * z * n = z * t := by
      calc n⁻¹ * z * n = n⁻¹ * (n * (z * t) * n⁻¹) * n := by rw [← hz']
        _ = z * t := by group
    have hcz : c * z * c⁻¹ = z * (t * (n * (m * t * m⁻¹) * n⁻¹)) := by
      calc c * z * c⁻¹ = n * m * (n⁻¹ * (m⁻¹ * z * m) * n) * m⁻¹ * n⁻¹ := by rw [hc]; group
        _ = n * m * (n⁻¹ * z * n) * m⁻¹ * n⁻¹ := by rw [hmz']
        _ = n * m * (z * t) * m⁻¹ * n⁻¹ := by rw [hnz']
        _ = n * (m * z * m⁻¹) * (m * t * m⁻¹) * n⁻¹ := by group
        _ = n * z * (m * t * m⁻¹) * n⁻¹ := by rw [hmz]
        _ = (n * z * n⁻¹) * (n * (m * t * m⁻¹) * n⁻¹) := by group
        _ = z * t * (n * (m * t * m⁻¹) * n⁻¹) := by rw [hnz]
        _ = z * (t * (n * (m * t * m⁻¹) * n⁻¹)) := by rw [mul_assoc]
    have hcF1 : ∀ x, x ∈ F1 ↔ c * x * c⁻¹ ∈ F1 := by
      intro x
      have e1 := D.m_F1 (m⁻¹ * x * m)
      rw [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at e1
      have e2 := hB1 (n⁻¹ * (m⁻¹ * x * m) * n)
      rw [show n * (n⁻¹ * (m⁻¹ * x * m) * n) * n⁻¹ = m⁻¹ * x * m by group] at e2
      have e3 := D.m_F2 (n⁻¹ * (m⁻¹ * x * m) * n)
      have e4 := hB1 (m * (n⁻¹ * (m⁻¹ * x * m) * n) * m⁻¹)
      rw [show n * (m * (n⁻¹ * (m⁻¹ * x * m) * n) * m⁻¹) * n⁻¹ = c * x * c⁻¹ by
        rw [hc]; group] at e4
      exact e1.symm.trans (e2.symm.trans (e3.trans e4))
    have hmt : m * t * m⁻¹ ∈ F2 := (D.m_F2 t).1 D.t_mem_F2
    have hs : t * (n * (m * t * m⁻¹) * n⁻¹) ∈ F1 :=
      Subgroup.mul_mem _ D.t_mem_F1 ((hB1 _).1 hmt)
    have hs1 : t * (n * (m * t * m⁻¹) * n⁻¹) ≠ 1 := by
      intro hX
      have h1 : n * (m * t * m⁻¹) * n⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right hX
      rw [inv_eq_of_mul_eq_one_right h.t_mul_self] at h1
      exact D.m_t (mul_left_cancel (mul_right_cancel (h1.trans hnt.symm)))
    exact ⟨c, mem_normalizer_sup h hF1L hcF1 hs hcz, _, hs, hs1, hcz⟩

theorem exists_normalizer_conj_eq_mul [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h : OneClassData L z t)
    (D : FusionData L t T1 F1 F2 m)
    (htrans : ∀ f ∈ F1, f ≠ 1 → ∀ f' ∈ F1, f' ≠ 1 →
      ∃ b ∈ L, (∀ x, x ∈ F1 ↔ b * x * b⁻¹ ∈ F1) ∧ b * f * b⁻¹ = f')
    (f : G) (hf : f ∈ F1) :
    ∃ c : G, (∀ x, x ∈ F1 ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F1 ⊔ zpowers z) ∧ c * z * c⁻¹ = z * f := by
  have hF1L : F1 ≤ L := D.F1_le.trans D.T1_le
  by_cases hf1 : f = 1
  · refine ⟨1, fun x => by simp, ?_⟩
    rw [hf1]
    group
  obtain ⟨c, hc, s, hs, hs1, hcz⟩ := exists_normalizer_moving_z hnonab h D
  obtain ⟨b, hbL, hbF, hbs⟩ := htrans s hs hs1 f hf hf1
  have hbz : b * z * b⁻¹ = z := by
    rw [← h.z_comm b hbL]
    group
  have hbE : ∀ x, x ∈ F1 ⊔ zpowers z ↔ b * x * b⁻¹ ∈ F1 ⊔ zpowers z :=
    mem_normalizer_sup h hF1L hbF (Subgroup.one_mem _) (by rw [hbz, mul_one])
  refine ⟨b * c, fun x => ?_, ?_⟩
  · calc x ∈ F1 ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F1 ⊔ zpowers z := hc x
      _ ↔ b * (c * x * c⁻¹) * b⁻¹ ∈ F1 ⊔ zpowers z := hbE _
      _ ↔ b * c * x * (b * c)⁻¹ ∈ F1 ⊔ zpowers z := by
        rw [show b * (c * x * c⁻¹) * b⁻¹ = b * c * x * (b * c)⁻¹ by group]
  · calc b * c * z * (b * c)⁻¹ = b * (c * z * c⁻¹) * b⁻¹ := by group
      _ = (b * z * b⁻¹) * (b * s * b⁻¹) := by rw [hcz]; group
      _ = z * f := by rw [hbz, hbs]

end Main


end CFSG.EvenSporadicStandard.M23Std
