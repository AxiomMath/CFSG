module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Local
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup

namespace A3Dich

variable {G : Type} [Group G]

theorem mem_sup_iff_of_le_normalizer {A B : Subgroup G} (h : A ≤ normalizer (B : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B h]
  exact Set.mem_mul

theorem mem_normalizer_of_forall_comm {B : Subgroup G} {g : G} (h : ∀ b ∈ B, g * b = b * g) :
    g ∈ normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have h1 := h _ hb
    have h2 : g * (g * b * g⁻¹) = g * b := by
      rw [h1]; group
    have h3 : g * b * g⁻¹ = b := mul_left_cancel h2
    rwa [h3] at hb

theorem mem_normalizer_inf {A B : Subgroup G} {h : G} (hA : h ∈ normalizer (A : Set G))
    (hB : h ∈ normalizer (B : Set G)) : h ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  exact and_congr (hA y) (hB y)

theorem card_conjSubgroup [Finite G] (A : Subgroup G) (g : G) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  card_map_equiv (MulAut.conj g⁻¹) A

theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g :=
  Subgroup.map_sup _ _ _

theorem conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conjSubgroup_le_of_le {S A : Subgroup G} {x : G} (hAS : A ≤ S)
    (hx : x ∈ normalizer (S : Set G)) : conjSubgroup A x ≤ S := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h2 := (mem_normalizer_iff.mp (inv_mem hx) (x * y * x⁻¹)).mp (hAS hy)
  simpa [mul_assoc] using h2

theorem le_normalizer_conjSubgroup {S A : Subgroup G} {x : G}
    (hSA : S ≤ normalizer (A : Set G)) (hx : x ∈ normalizer (S : Set G)) :
    S ≤ normalizer ((conjSubgroup A x : Subgroup G) : Set G) := by
  intro s hs
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
  have ht : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx s).mp hs
  have h1 : conjSubgroup A (x * s * x⁻¹) = A :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hSA ht)
  calc conjSubgroup A (x * s) = conjSubgroup A ((x * s * x⁻¹) * x) := by
        rw [inv_mul_cancel_right]
    _ = conjSubgroup (conjSubgroup A (x * s * x⁻¹)) x := (conjSubgroup_conjSubgroup _ _ _).symm
    _ = conjSubgroup A x := by rw [h1]

theorem conjSubgroup_conjSubgroup_self {A : Subgroup G} {x : G}
    (hx2 : x ^ 2 ∈ normalizer (A : Set G)) : conjSubgroup (conjSubgroup A x) x = A := by
  rw [conjSubgroup_conjSubgroup, ← pow_two]
  exact conjSubgroup_eq_iff_mem_normalizer.mpr hx2

theorem comm_of_inf_eq_bot {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hSA : S ≤ normalizer (A : Set G)) (hSB : S ≤ normalizer (B : Set G)) (h : A ⊓ B = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ ∈ B := (mem_normalizer_iff.mp (hSB (hAS ha)) b).mp hb
  have hB : a * b * a⁻¹ * b⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hb)
  have hA : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have h3 : b * a⁻¹ * b⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (hSA (hBS hb)) a⁻¹).mp (A.inv_mem ha)
    have := A.mul_mem ha h3
    simpa [mul_assoc] using this
  have h4 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨hA, hB⟩
  rw [h, Subgroup.mem_bot] at h4
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h4, one_mul]

variable [Finite G]

theorem eq_of_le_of_card {U K R : Subgroup G} (hUK : U ≤ K) (hKR : K ≤ R)
    (hU : Nat.card U = 4) (hR : Nat.card R = 8) (hne : K ≠ R) : K = U := by
  have h1 : Nat.card U ∣ Nat.card K := Subgroup.card_dvd_of_le hUK
  have h2 : Nat.card K ∣ Nat.card R := Subgroup.card_dvd_of_le hKR
  rw [hU] at h1
  rw [hR] at h2
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hle : Nat.card K ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  have hK : Nat.card K = 4 := by
    obtain ⟨k, hk⟩ := h1
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · omega
    · exact absurd (Subgroup.eq_of_le_of_card_ge hKR (by omega)) hne
  exact (Subgroup.eq_of_le_of_card_ge hUK (by omega)).symm

structure Data (S L U D : Subgroup G) (x : G) : Prop where
  card_U : Nat.card U = 4
  U_comm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u
  U_le : U ≤ S
  D_le : D ≤ S
  U_inf_D : U ⊓ D = ⊥
  S_cent_U : S ⊓ centralizer (U : Set G) = U ⊔ D
  card_S : Nat.card S = 8 * Nat.card D
  S_norm_U : S ≤ normalizer (U : Set G)
  S_norm_D : S ≤ normalizer (D : Set G)
  L_norm_U : L ≤ normalizer (U : Set G)
  D_comm_L : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d
  x_norm : x ∈ normalizer (S : Set G)
  x_sq : x ^ 2 ∈ S
  h244 : ∀ S₀ : Subgroup G, S₀ ≠ ⊥ → S₀ ≤ S → S ≤ normalizer (S₀ : Set G) →
    L ≤ normalizer (S₀ : Set G) → x ∈ normalizer (S₀ : Set G) → False

namespace Data

variable {S L U D : Subgroup G} {x : G}

omit [Finite G] in
theorem U_ne_bot (hd : Data S L U D x) : U ≠ ⊥ := by
  intro h
  have := hd.card_U
  rw [h, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem U'_le (hd : Data S L U D x) : conjSubgroup U x ≤ S :=
  conjSubgroup_le_of_le hd.U_le hd.x_norm

omit [Finite G] in
theorem S_norm_U' (hd : Data S L U D x) :
    S ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) :=
  le_normalizer_conjSubgroup hd.S_norm_U hd.x_norm

theorem card_U' (hd : Data S L U D x) : Nat.card (conjSubgroup U x) = 4 := by
  rw [card_conjSubgroup, hd.card_U]

omit [Finite G] in
theorem U'_conj (hd : Data S L U D x) : conjSubgroup (conjSubgroup U x) x = U :=
  conjSubgroup_conjSubgroup_self (hd.S_norm_U hd.x_sq)

omit [Finite G] in
theorem U'_comm (hd : Data S L U D x) :
    ∀ a ∈ conjSubgroup U x, ∀ b ∈ conjSubgroup U x, a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSubgroup_iff] at ha hb
  have h1 := hd.U_comm _ ha _ hb
  have h2 : x * (a * b) * x⁻¹ = x * (b * a) * x⁻¹ := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (x * b * x⁻¹) * (x * a * x⁻¹) := h1
      _ = x * (b * a) * x⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

omit [Finite G] in
theorem D'_le (hd : Data S L U D x) : conjSubgroup D x ≤ S :=
  conjSubgroup_le_of_le hd.D_le hd.x_norm

omit [Finite G] in
theorem S_norm_D' (hd : Data S L U D x) :
    S ≤ normalizer ((conjSubgroup D x : Subgroup G) : Set G) :=
  le_normalizer_conjSubgroup hd.S_norm_D hd.x_norm

omit [Finite G] in
theorem D'_conj (hd : Data S L U D x) : conjSubgroup (conjSubgroup D x) x = D :=
  conjSubgroup_conjSubgroup_self (hd.S_norm_D hd.x_sq)

omit [Finite G] in
theorem R_le (hd : Data S L U D x) : U ⊔ conjSubgroup U x ≤ S := sup_le hd.U_le hd.U'_le

omit [Finite G] in
theorem S_norm_R (hd : Data S L U D x) :
    S ≤ normalizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) := fun _ hs =>
  A3Gen.mem_normalizer_sup (hd.S_norm_U hs) (hd.S_norm_U' hs)

omit [Finite G] in
theorem R_conj (hd : Data S L U D x) :
    conjSubgroup (U ⊔ conjSubgroup U x) x = U ⊔ conjSubgroup U x := by
  rw [conjSubgroup_sup, hd.U'_conj, sup_comm]

omit [Finite G] in
theorem not_U'_le_Q (hd : Data S L U D x) : ¬ conjSubgroup U x ≤ U ⊔ D := by
  intro hle
  have hDU : D ≤ normalizer (U : Set G) := hd.D_le.trans hd.S_norm_U
  have hR₀eq : U ⊔ conjSubgroup U x = U ⊔ ((U ⊔ conjSubgroup U x) ⊓ D) := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      intro u' hu'
      have hu'Q : u' ∈ D ⊔ U := by
        rw [sup_comm]; exact hle hu'
      obtain ⟨d, hdD, u, hu, rfl⟩ := (mem_sup_iff_of_le_normalizer hDU).mp hu'Q
      have hdR : d ∈ U ⊔ conjSubgroup U x := by
        have h1 : d * u * u⁻¹ ∈ U ⊔ conjSubgroup U x :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_right hu')
            (Subgroup.inv_mem _ (Subgroup.mem_sup_left hu))
        simpa using h1
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hdR, hdD⟩) (Subgroup.mem_sup_left hu)
    · exact sup_le le_sup_left inf_le_left
  have hLR : L ≤ normalizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) := by
    intro l hl
    have : l ∈ normalizer ((U ⊔ ((U ⊔ conjSubgroup U x) ⊓ D) : Subgroup G) : Set G) :=
      A3Gen.mem_normalizer_sup (hd.L_norm_U hl)
        (mem_normalizer_of_forall_comm fun b hb => (hd.D_comm_L b hb.2 l hl).symm)
    rwa [← hR₀eq] at this
  have hxR : x ∈ normalizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hd.R_conj
  refine hd.h244 (U ⊔ conjSubgroup U x) ?_ hd.R_le hd.S_norm_R hLR hxR
  intro h
  have : U ≤ U ⊔ conjSubgroup U x := le_sup_left
  rw [h] at this
  exact hd.U_ne_bot (le_bot_iff.mp this)

omit [Finite G] in
theorem exists_noncomm (hd : Data S L U D x) :
    ∃ u ∈ U, ∃ u' ∈ conjSubgroup U x, u * u' ≠ u' * u := by
  by_contra hcon
  apply hd.not_U'_le_Q
  intro u' hu'
  rw [← hd.S_cent_U]
  refine Subgroup.mem_inf.mpr ⟨hd.U'_le hu', ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  by_contra hne
  exact hcon ⟨u, hu, u', hu', hne⟩

theorem card_inter (hd : Data S L U D x) : Nat.card ↥(U ⊓ conjSubgroup U x) = 2 := by
  obtain ⟨u, hu, u', hu', hne⟩ := hd.exists_noncomm
  have hu'S : u' ∈ S := hd.U'_le hu'
  have huS : u ∈ S := hd.U_le hu
  have h1 : u' * u⁻¹ * u'⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (hd.S_norm_U hu'S) u⁻¹).mp (U.inv_mem hu)
  have hU_e : u * (u' * u⁻¹ * u'⁻¹) ∈ U := U.mul_mem hu h1
  have h2 : u * u' * u⁻¹ ∈ conjSubgroup U x :=
    (mem_normalizer_iff.mp (hd.S_norm_U' huS) u').mp hu'
  have hU'_e : u * (u' * u⁻¹ * u'⁻¹) ∈ conjSubgroup U x := by
    have := (conjSubgroup U x).mul_mem h2 ((conjSubgroup U x).inv_mem hu')
    simpa [mul_assoc] using this
  have he1 : u * (u' * u⁻¹ * u'⁻¹) ≠ 1 := by
    intro h
    apply hne
    calc u * u' = (u * (u' * u⁻¹ * u'⁻¹)) * (u' * u) := by group
      _ = u' * u := by rw [h, one_mul]
  have hE : Nat.card ↥(U ⊓ conjSubgroup U x) ∣ 4 :=
    hd.card_U ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne1 : Nat.card ↥(U ⊓ conjSubgroup U x) ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    have : u * (u' * u⁻¹ * u'⁻¹) ∈ U ⊓ conjSubgroup U x := ⟨hU_e, hU'_e⟩
    rw [h, Subgroup.mem_bot] at this
    exact he1 this
  have hne4 : Nat.card ↥(U ⊓ conjSubgroup U x) ≠ 4 := by
    intro h
    have : U ⊓ conjSubgroup U x = conjSubgroup U x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hd.card_U'])
    apply hd.not_U'_le_Q
    rw [← this]
    exact inf_le_left.trans le_sup_left
  have hle : Nat.card ↥(U ⊓ conjSubgroup U x) ≤ 4 := Nat.le_of_dvd (by norm_num) hE
  generalize Nat.card ↥(U ⊓ conjSubgroup U x) = n at *
  interval_cases n <;> omega

theorem card_R (hd : Data S L U D x) : Nat.card ↥(U ⊔ conjSubgroup U x) = 8 := by
  have h := A3Gen.card_sup_mul_card_inf_of_le_normalizer' (A := U) (B := conjSubgroup U x)
    (hd.U_le.trans hd.S_norm_U')
  rw [hd.card_U, hd.card_U', hd.card_inter] at h
  omega

theorem R_inf_Q (hd : Data S L U D x) : (U ⊔ conjSubgroup U x) ⊓ (U ⊔ D) = U := by
  refine eq_of_le_of_card (U := U) (R := U ⊔ conjSubgroup U x) ?_ inf_le_left hd.card_U
    hd.card_R ?_
  · exact le_inf le_sup_left le_sup_left
  · intro h
    apply hd.not_U'_le_Q
    have : U ⊔ conjSubgroup U x ≤ U ⊔ D := h.symm.le.trans inf_le_right
    exact le_sup_right.trans this

theorem R_inf_D (hd : Data S L U D x) : (U ⊔ conjSubgroup U x) ⊓ D = ⊥ := by
  have h1 : (U ⊔ conjSubgroup U x) ⊓ D ≤ U ⊓ D := by
    refine le_inf ?_ inf_le_right
    exact (le_inf inf_le_left (inf_le_right.trans le_sup_right)).trans hd.R_inf_Q.le
  rw [hd.U_inf_D] at h1
  exact le_bot_iff.mp h1

theorem S_eq_R_sup_D (hd : Data S L U D x) : S = (U ⊔ conjSubgroup U x) ⊔ D := by
  have hle : (U ⊔ conjSubgroup U x) ⊔ D ≤ S := sup_le hd.R_le hd.D_le
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h := A3Gen.card_sup_mul_card_inf_of_le_normalizer' (A := D)
    (B := U ⊔ conjSubgroup U x) (hd.D_le.trans hd.S_norm_R)
  rw [inf_comm, hd.R_inf_D, Subgroup.card_bot, hd.card_R,
    sup_comm D (U ⊔ conjSubgroup U x)] at h
  have := hd.card_S
  omega

theorem R_comm_D (hd : Data S L U D x) :
    ∀ r ∈ U ⊔ conjSubgroup U x, ∀ d ∈ D, r * d = d * r :=
  comm_of_inf_eq_bot hd.R_le hd.D_le hd.S_norm_R hd.S_norm_D hd.R_inf_D

omit [Finite G] in
theorem D_inf_D' (hd : Data S L U D x) : D ⊓ conjSubgroup D x = ⊥ := by
  by_contra hne
  refine hd.h244 (D ⊓ conjSubgroup D x) hne (inf_le_left.trans hd.D_le) ?_ ?_ ?_
  · intro s hs
    exact mem_normalizer_inf (hd.S_norm_D hs) (hd.S_norm_D' hs)
  · intro l hl
    exact mem_normalizer_of_forall_comm fun b hb => (hd.D_comm_L b hb.1 l hl).symm
  · rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_inf, hd.D'_conj, inf_comm]

theorem S_eq_R_sup_D' (hd : Data S L U D x) : S = (U ⊔ conjSubgroup U x) ⊔ conjSubgroup D x := by
  have hS : conjSubgroup S x = S := conjSubgroup_eq_iff_mem_normalizer.mpr hd.x_norm
  calc S = conjSubgroup S x := hS.symm
    _ = conjSubgroup ((U ⊔ conjSubgroup U x) ⊔ D) x := by rw [← hd.S_eq_R_sup_D]
    _ = conjSubgroup (U ⊔ conjSubgroup U x) x ⊔ conjSubgroup D x := conjSubgroup_sup _ _ _
    _ = (U ⊔ conjSubgroup U x) ⊔ conjSubgroup D x := by rw [hd.R_conj]

theorem R_inf_D' (hd : Data S L U D x) : (U ⊔ conjSubgroup U x) ⊓ conjSubgroup D x = ⊥ := by
  have h := A3Gen.card_sup_mul_card_inf_of_le_normalizer' (A := conjSubgroup D x)
    (B := U ⊔ conjSubgroup U x) (hd.D'_le.trans hd.S_norm_R)
  rw [sup_comm (conjSubgroup D x) (U ⊔ conjSubgroup U x), ← hd.S_eq_R_sup_D', hd.card_S,
    card_conjSubgroup D x, hd.card_R, inf_comm] at h
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h1 : Nat.card ↥((U ⊔ conjSubgroup U x) ⊓ conjSubgroup D x) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8 * Nat.card D) ?_
    rw [h]; ring
  exact Subgroup.card_eq_one.mp h1

theorem R_comm_D' (hd : Data S L U D x) :
    ∀ r ∈ U ⊔ conjSubgroup U x, ∀ d ∈ conjSubgroup D x, r * d = d * r :=
  comm_of_inf_eq_bot hd.R_le hd.D'_le hd.S_norm_R hd.S_norm_D' hd.R_inf_D'

theorem R_inf_centralizer_U (hd : Data S L U D x) :
    (U ⊔ conjSubgroup U x) ⊓ centralizer (U : Set G) = U := by
  obtain ⟨u, hu, u', hu', hne⟩ := hd.exists_noncomm
  refine eq_of_le_of_card (U := U) (R := U ⊔ conjSubgroup U x) ?_ inf_le_left hd.card_U
    hd.card_R ?_
  · exact le_inf le_sup_left fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => hd.U_comm h hh a ha
  · intro h
    apply hne
    have hle : U ⊔ conjSubgroup U x ≤ centralizer (U : Set G) := h.symm.le.trans inf_le_right
    exact Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_sup_right hu')) u hu

theorem R_inf_centralizer_U' (hd : Data S L U D x) :
    (U ⊔ conjSubgroup U x) ⊓ centralizer ((conjSubgroup U x : Subgroup G) : Set G) =
      conjSubgroup U x := by
  obtain ⟨u, hu, u', hu', hne⟩ := hd.exists_noncomm
  refine eq_of_le_of_card (U := conjSubgroup U x) (R := U ⊔ conjSubgroup U x) ?_ inf_le_left
    hd.card_U' hd.card_R ?_
  · exact le_inf le_sup_right fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun h hh => hd.U'_comm h hh a ha
  · intro h
    apply hne
    have hle : U ⊔ conjSubgroup U x ≤ centralizer ((conjSubgroup U x : Subgroup G) : Set G) :=
      h.symm.le.trans inf_le_right
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_sup_left hu)) u' hu').symm

theorem card_Z_le (hd : Data S L U D x) :
    Nat.card ↥((U ⊔ conjSubgroup U x) ⊓
      centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G)) ≤ 2 := by
  have h1 : (U ⊔ conjSubgroup U x) ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) ≤
      U ⊓ conjSubgroup U x := by
    refine le_inf ?_ ?_
    · exact (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
        (fun a ha => Subgroup.mem_sup_left ha)))).trans hd.R_inf_centralizer_U.le
    · exact (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le
        (fun a ha => Subgroup.mem_sup_right ha)))).trans hd.R_inf_centralizer_U'.le
  have h2 := Subgroup.card_le_of_le h1
  rwa [hd.card_inter] at h2

theorem card_C_le (hd : Data S L U D x) :
    Nat.card ↥(S ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G)) ≤
      2 * Nat.card D := by
  have hCR : S ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) ≤
      normalizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) := inf_le_left.trans hd.S_norm_R
  have h := A3Gen.card_sup_mul_card_inf_of_le_normalizer' hCR
  have h1 : Nat.card ↥(S ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) ⊔
      (U ⊔ conjSubgroup U x)) ≤ Nat.card S :=
    Subgroup.card_le_of_le (sup_le inf_le_left hd.R_le)
  have h2 : S ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) ⊓
      (U ⊔ conjSubgroup U x) =
      (U ⊔ conjSubgroup U x) ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hR⟩
      exact ⟨hR, hc⟩
    · rintro ⟨hR, hc⟩
      exact ⟨⟨hd.R_le hR, hc⟩, hR⟩
  have hz := hd.card_Z_le
  rw [← h2] at hz
  have hm := Nat.mul_le_mul (hd.card_S ▸ h1) hz
  rw [h, hd.card_R] at hm
  omega

theorem card_D_le_two (hd : Data S L U D x) : Nat.card D ≤ 2 := by
  have hDC : D ⊔ conjSubgroup D x ≤
      S ⊓ centralizer ((U ⊔ conjSubgroup U x : Subgroup G) : Set G) := by
    refine sup_le (le_inf hd.D_le ?_) (le_inf hd.D'_le ?_)
    · intro d hdD
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hd.R_comm_D r hr d hdD
    · intro d hdD
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hd.R_comm_D' r hr d hdD
  have h1 := Subgroup.card_le_of_le hDC
  have h2 := A3Gen.card_sup_mul_card_inf_of_le_normalizer' (A := D) (B := conjSubgroup D x)
    (hd.D_le.trans hd.S_norm_D')
  rw [hd.D_inf_D', Subgroup.card_bot, card_conjSubgroup D x] at h2
  have h3 := hd.card_C_le
  have hpos : 0 < Nat.card D := Nat.card_pos
  nlinarith

theorem main (hd : Data S L U D x) :
    Nat.card D ≤ 2 ∧ Nat.card ↥(U ⊔ conjSubgroup U x) = 8 ∧
      (∃ r ∈ U ⊔ conjSubgroup U x, ∃ s ∈ U ⊔ conjSubgroup U x, r * s ≠ s * r) ∧
      U ⊔ conjSubgroup U x ≤ S ∧ (U ⊔ conjSubgroup U x) ⊓ D = ⊥ ∧
      S = (U ⊔ conjSubgroup U x) ⊔ D := by
  obtain ⟨u, hu, u', hu', hne⟩ := hd.exists_noncomm
  exact ⟨hd.card_D_le_two, hd.card_R,
    ⟨u, Subgroup.mem_sup_left hu, u', Subgroup.mem_sup_right hu', hne⟩,
    hd.R_le, hd.R_inf_D, hd.S_eq_R_sup_D⟩

end Data

end A3Dich

end CFSG.QuasithinUnique
