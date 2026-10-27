module

public import CFSG.ClassicalInvolution.Asc77.AscP1Thompson3T

public section

namespace CFSG.ClassicalInvolution.Asc77.Star3T

variable {Q : Type*} [Group Q] {Δ : Set Q}

@[expose] def transl (a d y : Q) : Q := a * y * d * a

structure Cfg (Δ : Set Q) (d a : Q) : Prop where
  tt : IsTT Δ
  star : IsStar Δ
  mem_d : d ∈ Δ
  mem_a : a ∈ Δ
  not_conn : ¬ Conn Δ d a

namespace Cfg

variable {d a : Q} (c : Cfg Δ d a)
include c

theorem plane : IsPlane Δ d a (d * a * d) := ⟨c.mem_d, c.mem_a, c.not_conn, rfl⟩

theorem comm_cent {u v : Q} (hu : u ∈ cent Δ d) (hv : v ∈ cent Δ d) : u * v = v * u :=
  c.tt.isClique_cent c.star c.mem_d c.mem_a c.not_conn hu hv

theorem noncomm_a {y : Q} (hy : y ∈ cent Δ d) : y * a ≠ a * y := fun e =>
  c.not_conn ((conn_of_mem_cent c.mem_d hy).trans (conn_of_commute hy.1 c.mem_a e))

theorem braid_da : d * a * d = a * d * a :=
  c.tt.braid c.mem_d c.mem_a (fun e => c.not_conn (conn_of_commute c.mem_d c.mem_a e))

theorem braid_ya {y : Q} (hy : y ∈ cent Δ d) : y * a * y = a * y * a :=
  c.tt.braid hy.1 c.mem_a (c.noncomm_a hy)

theorem transl_sq {y : Q} (hy : y ∈ cent Δ d) : transl a d y * transl a d y = 1 := by
  have haa := c.tt.mul_self a c.mem_a
  have he : (y * d) * (y * d) = 1 := c.tt.mul_mul_self_of_commute hy.1 c.mem_d hy.2
  unfold transl
  calc a * y * d * a * (a * y * d * a) = a * (y * d) * (a * a) * (y * d) * a := by
        simp only [mul_assoc]
    _ = a * (y * d) * (y * d) * a := by rw [haa, mul_one]
    _ = a * ((y * d) * (y * d)) * a := by simp only [mul_assoc]
    _ = a * a := by rw [he, mul_one]
    _ = 1 := haa

theorem transl_inv {y : Q} (hy : y ∈ cent Δ d) : (transl a d y)⁻¹ = transl a d y :=
  inv_eq_of_mul_eq_one_left (c.transl_sq hy)

theorem transl_comm {y y' : Q} (hy : y ∈ cent Δ d) (hy' : y' ∈ cent Δ d) :
    transl a d y * transl a d y' = transl a d y' * transl a d y := by
  have haa := c.tt.mul_self a c.mem_a
  have c1 : Commute y y' := c.comm_cent hy hy'
  have c2 : Commute y d := hy.2
  have c3 : Commute y' d := hy'.2
  have h1 : (y * d) * (y' * d) = (y' * d) * (y * d) :=
    (Commute.mul_left (c1.mul_right c2) ((c3.symm).mul_right (Commute.refl d))).eq
  unfold transl
  calc a * y * d * a * (a * y' * d * a) = a * ((y * d) * (y' * d)) * a := by
        calc a * y * d * a * (a * y' * d * a)
            = a * (y * d) * (a * a) * (y' * d) * a := by simp only [mul_assoc]
          _ = a * ((y * d) * (y' * d)) * a := by rw [haa, mul_one]; simp only [mul_assoc]
    _ = a * ((y' * d) * (y * d)) * a := by rw [h1]
    _ = a * y' * d * a * (a * y * d * a) := by
        calc a * ((y' * d) * (y * d)) * a = a * (y' * d) * (a * a) * (y * d) * a := by
              rw [haa, mul_one]; simp only [mul_assoc]
          _ = a * y' * d * a * (a * y * d * a) := by simp only [mul_assoc]

theorem transl_act_d {y : Q} (hy : y ∈ cent Δ d) : transl a d y * d * transl a d y = y := by
  have haa := c.tt.mul_self a c.mem_a
  have hdd := c.tt.mul_self d c.mem_d
  have bda := c.braid_da
  have bya := c.braid_ya hy
  have hyd : y * d = d * y := hy.2
  have hdyd : d * y * d = y := by
    calc d * y * d = y * d * d := by rw [← hyd]
      _ = y := by rw [mul_assoc, hdd, mul_one]
  unfold transl
  calc a * y * d * a * d * (a * y * d * a) = a * y * d * (a * d * a) * y * d * a := by
        simp only [mul_assoc]
    _ = a * y * d * (d * a * d) * y * d * a := by rw [← bda]
    _ = a * y * (d * d) * a * (d * y * d) * a := by simp only [mul_assoc]
    _ = a * y * a * y * a := by rw [hdd, mul_one, hdyd]
    _ = a * (y * a * y) * a := by simp only [mul_assoc]
    _ = a * (a * y * a) * a := by rw [bya]
    _ = (a * a) * y * (a * a) := by simp only [mul_assoc]
    _ = y := by rw [haa, one_mul, mul_one]

theorem transl_act_mem {y x : Q} (hy : y ∈ cent Δ d) (hx : x ∈ cent Δ d) :
    transl a d y * x * transl a d y ∈ cent Δ d := by
  set τ := transl a d y with hτ
  have hτ1 : τ * τ = 1 := c.transl_sq hy
  have hτd : τ * d * τ = y := c.transl_act_d hy
  have hτd1 : τ * d = y * τ := by
    calc τ * d = τ * d * (τ * τ) := by rw [hτ1, mul_one]
      _ = (τ * d * τ) * τ := by simp only [mul_assoc]
      _ = y * τ := by rw [hτd]
  have hdτ : d * τ = τ * y := by
    calc d * τ = (τ * τ) * d * τ := by rw [hτ1, one_mul]
      _ = τ * (τ * d * τ) := by simp only [mul_assoc]
      _ = τ * y := by rw [hτd]
  have hmem : τ * x * τ ∈ Δ := by
    have := c.tt.conj_mem' hx.1 τ
    rwa [c.transl_inv hy] at this
  refine ⟨hmem, ?_⟩
  have hxy : x * y = y * x := c.comm_cent hx hy
  calc τ * x * τ * d = τ * x * (τ * d) := by simp only [mul_assoc]
    _ = τ * x * (y * τ) := by rw [hτd1]
    _ = τ * (x * y) * τ := by simp only [mul_assoc]
    _ = τ * (y * x) * τ := by rw [hxy]
    _ = (τ * y) * x * τ := by simp only [mul_assoc]
    _ = (d * τ) * x * τ := by rw [hdτ]
    _ = d * (τ * x * τ) := by simp only [mul_assoc]

end Cfg

@[expose] def translGroup (a d : Q) (B : Set Q) : Subgroup Q :=
  Subgroup.closure (transl a d '' B)

@[expose] def orbitSet (a d : Q) (B : Set Q) : Set Q :=
  {x | ∃ g ∈ translGroup a d B, x = g * d * g⁻¹}

theorem transl_mem_translGroup {a d : Q} {B : Set Q} {y : Q} (hy : y ∈ B) :
    transl a d y ∈ translGroup a d B :=
  Subgroup.subset_closure ⟨y, hy, rfl⟩

theorem translGroup_mono {a d : Q} {B B' : Set Q} (h : B ⊆ B') :
    translGroup a d B ≤ translGroup a d B' :=
  Subgroup.closure_mono (Set.image_mono h)

theorem orbitSet_mono {a d : Q} {B B' : Set Q} (h : B ⊆ B') : orbitSet a d B ⊆ orbitSet a d B' :=
  fun _ ⟨g, hg, hx⟩ => ⟨g, translGroup_mono h hg, hx⟩

theorem d_mem_orbitSet {a d : Q} {B : Set Q} : d ∈ orbitSet a d B :=
  ⟨1, Subgroup.one_mem _, by simp⟩

namespace Cfg

variable {d a : Q} (c : Cfg Δ d a)
include c

theorem mem_orbitSet_of_mem {B : Set Q} (hB : B ⊆ cent Δ d) {y : Q} (hy : y ∈ B) :
    y ∈ orbitSet a d B := by
  refine ⟨transl a d y, transl_mem_translGroup hy, ?_⟩
  rw [c.transl_inv (hB hy)]
  exact (c.transl_act_d (hB hy)).symm

theorem comm_translGroup {B : Set Q} (hB : B ⊆ cent Δ d) {g y : Q}
    (hg : g ∈ translGroup a d B) (hy : y ∈ cent Δ d) :
    g * transl a d y = transl a d y * g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact c.transl_comm (hB hb) hy
  | one => simp
  | mul x z _ _ hx hz =>
    calc x * z * transl a d y = x * (z * transl a d y) := mul_assoc _ _ _
      _ = x * (transl a d y * z) := by rw [hz]
      _ = (x * transl a d y) * z := (mul_assoc _ _ _).symm
      _ = transl a d y * x * z := by rw [hx]
      _ = transl a d y * (x * z) := mul_assoc _ _ _
  | inv x _ hx =>
    exact (Commute.inv_left (show Commute x (transl a d y) from hx)).eq

theorem commute_translGroup {B B' : Set Q} (hB : B ⊆ cent Δ d) (hB' : B' ⊆ cent Δ d) {g g' : Q}
    (hg : g ∈ translGroup a d B) (hg' : g' ∈ translGroup a d B') : g * g' = g' * g := by
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact c.comm_translGroup hB hg (hB' hb)
  | one => simp
  | mul x z _ _ hx hz =>
    calc g * (x * z) = (g * x) * z := (mul_assoc _ _ _).symm
      _ = (x * g) * z := by rw [hx]
      _ = x * (g * z) := mul_assoc _ _ _
      _ = x * (z * g) := by rw [hz]
      _ = (x * z) * g := (mul_assoc _ _ _).symm
  | inv x _ hx =>
    exact (Commute.inv_right (show Commute g x from hx)).eq

theorem conj_mem_cent {B : Set Q} (hB : B ⊆ cent Δ d) {g : Q} (hg : g ∈ translGroup a d B) :
    ∀ x ∈ cent Δ d, g * x * g⁻¹ ∈ cent Δ d ∧ g⁻¹ * x * g ∈ cent Δ d := by
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    intro x hx
    have := c.transl_act_mem (hB hb) hx
    rw [c.transl_inv (hB hb)]
    exact ⟨this, this⟩
  | one =>
    intro x hx
    simpa using hx
  | mul u v _ _ hu hv =>
    intro x hx
    obtain ⟨h1, -⟩ := hv x hx
    obtain ⟨-, h4⟩ := hu x hx
    refine ⟨?_, ?_⟩
    · have := (hu _ h1).1
      simpa [mul_assoc] using this
    · have := (hv _ h4).2
      simpa [mul_assoc] using this
  | inv u _ hu =>
    intro x hx
    exact ⟨by simpa using (hu x hx).2, by simpa using (hu x hx).1⟩

theorem orbitSet_subset_cent {B : Set Q} (hB : B ⊆ cent Δ d) : orbitSet a d B ⊆ cent Δ d := by
  rintro x ⟨g, hg, rfl⟩
  exact (c.conj_mem_cent hB hg d (self_mem_cent c.mem_d)).1

theorem act_trivial {g : Q} (hg : g ∈ translGroup a d (cent Δ d)) (hgd : g * d * g⁻¹ = d)
    {x : Q} (hx : x ∈ cent Δ d) : g * x * g⁻¹ = x := by
  have hτ := c.comm_translGroup (subset_refl _) hg hx
  have hτg : g * transl a d x * g⁻¹ = transl a d x := by
    rw [hτ]
    group
  have hxe := c.transl_act_d hx
  calc g * x * g⁻¹ = g * (transl a d x * d * transl a d x) * g⁻¹ := by rw [hxe]
    _ = (g * transl a d x * g⁻¹) * (g * d * g⁻¹) * (g * transl a d x * g⁻¹) := by group
    _ = transl a d x * d * transl a d x := by rw [hτg, hgd]
    _ = x := hxe

theorem orbitSet_insert_eq {B : Set Q} (hB : B ⊆ cent Δ d) {x : Q} (hx : x ∈ cent Δ d) :
    orbitSet a d (insert x B) =
      orbitSet a d B ∪ (fun s => transl a d x * s * transl a d x) '' orbitSet a d B := by
  have hτ1 := c.transl_sq hx
  have hτi := c.transl_inv hx
  have key : ∀ g ∈ translGroup a d (insert x B),
      ∃ h ∈ translGroup a d B, g = h ∨ g = transl a d x * h := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨b, hb, rfl⟩ := ht
      rcases hb with rfl | hb
      · exact ⟨1, Subgroup.one_mem _, Or.inr (by simp)⟩
      · exact ⟨transl a d b, transl_mem_translGroup hb, Or.inl rfl⟩
    | one => exact ⟨1, Subgroup.one_mem _, Or.inl rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨h, hh, hu'⟩ := hu
      obtain ⟨h', hh', hv'⟩ := hv
      have hcomm : h * transl a d x = transl a d x * h := c.comm_translGroup hB hh hx
      refine ⟨h * h', (translGroup a d B).mul_mem hh hh', ?_⟩
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv']
      · exact Or.inl rfl
      · right
        calc h * (transl a d x * h') = (h * transl a d x) * h' := (mul_assoc _ _ _).symm
          _ = (transl a d x * h) * h' := by rw [hcomm]
          _ = transl a d x * (h * h') := mul_assoc _ _ _
      · right
        exact mul_assoc _ _ _
      · left
        calc transl a d x * h * (transl a d x * h')
            = transl a d x * (h * transl a d x) * h' := by simp only [mul_assoc]
          _ = transl a d x * (transl a d x * h) * h' := by rw [hcomm]
          _ = (transl a d x * transl a d x) * h * h' := by simp only [mul_assoc]
          _ = h * h' := by rw [hτ1, one_mul]
    | inv u _ hu =>
      obtain ⟨h, hh, hu'⟩ := hu
      refine ⟨h⁻¹, (translGroup a d B).inv_mem hh, ?_⟩
      rcases hu' with rfl | rfl
      · exact Or.inl rfl
      · right
        have hcomm : h * transl a d x = transl a d x * h := c.comm_translGroup hB hh hx
        calc (transl a d x * h)⁻¹ = h⁻¹ * (transl a d x)⁻¹ := mul_inv_rev _ _
          _ = h⁻¹ * transl a d x := by rw [hτi]
          _ = transl a d x * h⁻¹ := (Commute.inv_left (show Commute h (transl a d x) from hcomm)).eq
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h, hh, hg'⟩ := key g hg
    rcases hg' with rfl | rfl
    · exact Or.inl ⟨g, hh, rfl⟩
    · right
      refine ⟨h * d * h⁻¹, ⟨h, hh, rfl⟩, ?_⟩
      show transl a d x * (h * d * h⁻¹) * transl a d x =
        transl a d x * h * d * (transl a d x * h)⁻¹
      rw [mul_inv_rev, hτi]
      simp only [mul_assoc]
  · rintro (hs | ⟨t, ⟨h, hh, rfl⟩, rfl⟩)
    · exact orbitSet_mono (Set.subset_insert x B) hs
    · refine ⟨transl a d x * h, (translGroup a d (insert x B)).mul_mem
        (transl_mem_translGroup (Set.mem_insert _ _))
        (translGroup_mono (Set.subset_insert x B) hh), ?_⟩
      show transl a d x * (h * d * h⁻¹) * transl a d x =
        transl a d x * h * d * (transl a d x * h)⁻¹
      rw [mul_inv_rev, hτi]
      simp only [mul_assoc]

theorem disjoint_orbitSet_image {B : Set Q} (hB : B ⊆ cent Δ d) {x : Q} (hx : x ∈ cent Δ d)
    (hxB : x ∉ orbitSet a d B) :
    Disjoint (orbitSet a d B)
      ((fun s => transl a d x * s * transl a d x) '' orbitSet a d B) := by
  rw [Set.disjoint_left]
  rintro t ⟨h_t, hht, rfl⟩ ⟨s, ⟨h_s, hhs, rfl⟩, hts⟩
  have hτi := c.transl_inv hx
  have hts' : transl a d x * (h_s * d * h_s⁻¹) * transl a d x = h_t * d * h_t⁻¹ := hts
  have hCfull : (cent Δ d) ⊆ cent Δ d := subset_refl _
  have hAfull : ∀ y ∈ translGroup a d B, y ∈ translGroup a d (cent Δ d) :=
    fun y hy => translGroup_mono hB hy
  have hτA : transl a d x ∈ translGroup a d (cent Δ d) := transl_mem_translGroup hx
  set g := h_t⁻¹ * transl a d x * h_s with hg
  have hgA : g ∈ translGroup a d (cent Δ d) :=
    (translGroup a d (cent Δ d)).mul_mem
      ((translGroup a d (cent Δ d)).mul_mem
        ((translGroup a d (cent Δ d)).inv_mem (hAfull _ hht)) hτA) (hAfull _ hhs)
  have hgd : g * d * g⁻¹ = d := by
    have e : g * d * g⁻¹ = h_t⁻¹ * (transl a d x * (h_s * d * h_s⁻¹) * (transl a d x)⁻¹) * h_t := by
      rw [hg]
      group
    rw [e, hτi, hts']
    group
  have hc0 : h_s⁻¹ * d * h_s ∈ cent Δ d := by
    have := (c.conj_mem_cent hB ((translGroup a d B).inv_mem hhs) d
      (self_mem_cent c.mem_d)).1
    simpa using this
  have h1 := c.act_trivial hgA hgd hc0
  have e1 : g * (h_s⁻¹ * d * h_s) * g⁻¹ =
      h_t⁻¹ * (transl a d x * d * (transl a d x)⁻¹) * h_t := by
    rw [hg]
    group
  rw [e1, hτi, c.transl_act_d hx] at h1
  apply hxB
  refine ⟨h_t * h_s⁻¹, (translGroup a d B).mul_mem hht ((translGroup a d B).inv_mem hhs), ?_⟩
  calc x = h_t * (h_t⁻¹ * x * h_t) * h_t⁻¹ := by group
    _ = h_t * (h_s⁻¹ * d * h_s) * h_t⁻¹ := by rw [h1]
    _ = h_t * h_s⁻¹ * d * (h_t * h_s⁻¹)⁻¹ := by group

theorem ncard_orbitSet_insert [Finite Q] {B : Set Q} (hB : B ⊆ cent Δ d) {x : Q}
    (hx : x ∈ cent Δ d) (hxB : x ∉ orbitSet a d B) :
    (orbitSet a d (insert x B)).ncard = 2 * (orbitSet a d B).ncard := by
  have hinj : Function.Injective (fun s : Q => transl a d x * s * transl a d x) := fun s s' h => by
    have h' : transl a d x * s * transl a d x = transl a d x * s' * transl a d x := h
    exact mul_left_cancel (mul_right_cancel h')
  rw [c.orbitSet_insert_eq hB hx, Set.ncard_union_eq (c.disjoint_orbitSet_image hB hx hxB),
    Set.ncard_image_of_injective _ hinj]
  ring

theorem exists_good_family [Finite Q] :
    ∃ B : Finset Q, (↑B : Set Q) ⊆ cent Δ d ∧ d ∉ B ∧ orbitSet a d ↑B = cent Δ d ∧
      (cent Δ d).ncard = 2 ^ B.card := by
  classical
  have key : ∀ N : ℕ, ∀ B : Finset Q, (↑B : Set Q) ⊆ cent Δ d → d ∉ B →
      (orbitSet a d ↑B).ncard = 2 ^ B.card → (cent Δ d).ncard - (orbitSet a d ↑B).ncard = N →
      ∃ B' : Finset Q, (↑B' : Set Q) ⊆ cent Δ d ∧ d ∉ B' ∧ orbitSet a d ↑B' = cent Δ d ∧
        (cent Δ d).ncard = 2 ^ B'.card := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro B hBC hdB hcard hN
      by_cases hfull : orbitSet a d ↑B = cent Δ d
      · exact ⟨B, hBC, hdB, hfull, by rw [← hfull]; exact hcard⟩
      · have hsub := c.orbitSet_subset_cent hBC
        obtain ⟨x, hxC, hxO⟩ : ∃ x ∈ cent Δ d, x ∉ orbitSet a d ↑B := by
          by_contra hcon
          push Not at hcon
          exact hfull (Set.Subset.antisymm hsub hcon)
        have hxB : x ∉ B := fun hxB =>
          hxO (c.mem_orbitSet_of_mem hBC (Finset.mem_coe.mpr hxB))
        have hxd : x ≠ d := fun e => hxO (e ▸ d_mem_orbitSet)
        have hnew := c.ncard_orbitSet_insert hBC hxC hxO
        have hpos : 0 < (orbitSet a d ↑B).ncard :=
          (Set.ncard_pos (Set.toFinite _)).mpr ⟨d, d_mem_orbitSet⟩
        have hle1 : (orbitSet a d ↑B).ncard ≤ (cent Δ d).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        have hlt : (orbitSet a d ↑B).ncard < (cent Δ d).ncard := by
          refine lt_of_le_of_ne hle1 fun he => hfull ?_
          exact Set.eq_of_subset_of_ncard_le hsub he.ge (Set.toFinite _)
        refine ih ((cent Δ d).ncard - (orbitSet a d ↑(insert x B)).ncard) ?_ (insert x B) ?_ ?_ ?_
          rfl
        · rw [Finset.coe_insert, hnew]
          omega
        · rw [Finset.coe_insert]
          exact Set.insert_subset hxC hBC
        · intro hmem
          rcases Finset.mem_insert.mp hmem with e | e
          · exact hxd e.symm
          · exact hdB e
        · rw [Finset.coe_insert, hnew, Finset.card_insert_of_notMem hxB, hcard, pow_succ]
          ring
  exact key _ ∅ (by simp) (by simp)
    (by
      have : orbitSet a d (↑(∅ : Finset Q) : Set Q) = {d} := by
        ext y
        constructor
        · rintro ⟨g, hg, rfl⟩
          have : translGroup a d (↑(∅ : Finset Q) : Set Q) = ⊥ := by
            simp [translGroup]
          rw [this] at hg
          rw [Subgroup.mem_bot.mp hg]
          simp
        · rintro rfl
          exact d_mem_orbitSet
      rw [this]
      simp) rfl

theorem exists_generating_family [Finite Q] :
    ∃ n : ℕ, ∃ B : Finset Q, (cent Δ d).ncard = 2 ^ n ∧ (↑B : Set Q) ⊆ cent Δ d ∧ d ∈ B ∧
      B.card = n + 1 ∧ Subgroup.closure (insert a (B : Set Q)) = ⊤ := by
  classical
  obtain ⟨B₀, hB₀C, hdB₀, horb, hcard⟩ := c.exists_good_family
  refine ⟨B₀.card, insert d B₀, hcard, ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy'
    · exact self_mem_cent c.mem_d
    · exact hB₀C hy'
  · exact Finset.card_insert_of_notMem hdB₀
  · set H := Subgroup.closure (insert a (↑(insert d B₀) : Set Q)) with hH
    have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have hdH : d ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (by simp))
    have hbH : ∀ b ∈ B₀, b ∈ H := fun b hb =>
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (by simp [hb]))
    have hAH : translGroup a d ↑B₀ ≤ H := by
      rw [translGroup, Subgroup.closure_le]
      rintro _ ⟨b, hb, rfl⟩
      exact H.mul_mem (H.mul_mem (H.mul_mem haH (hbH b hb)) hdH) haH
    have hC : cent Δ d ⊆ H := by
      rw [← horb]
      rintro x ⟨g, hg, rfl⟩
      exact H.mul_mem (H.mul_mem (hAH hg) hdH) (H.inv_mem (hAH hg))
    have htop := c.tt.closure_insert_cent_eq_top c.star c.plane
    rw [eq_top_iff, ← htop]
    exact (Subgroup.closure_le H).mpr (Set.insert_subset haH hC)

end Cfg

end CFSG.ClassicalInvolution.Asc77.Star3T
