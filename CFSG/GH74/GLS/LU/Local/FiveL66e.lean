module

public import CFSG.GH74.GLS.LU.Local.FiveL66d

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section Toolkit

variable {G Gs : Type} [Group G] [Group Gs] {X : Subgroup G} {X' : Subgroup Gs}

theorem pull_cjL (ψ : ↥X ≃* ↥X') {g : G} (hg : g ∈ X) (E' : Subgroup Gs) :
    cjL g (pull ψ E') = pull ψ (cjL (pe ψ g hg) E') :=
  pull_map_conj ψ hg

theorem pull_centralizer_inf (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') :
    pull ψ (centralizer (E' : Set Gs) ⊓ X') = centralizer (pull ψ E' : Set G) ⊓ X := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · intro hx
    have hxX : x ∈ X := pull_le ψ _ hx
    have h := (mem_pull ψ _ hxX).mp hx
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, hxX⟩
    intro y hy
    have hyX : y ∈ X := pull_le ψ _ hy
    have hy' := (mem_pull ψ _ hyX).mp hy
    have h2 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).1 _ hy'
    exact (pe_comm_iff ψ hyX hxX).mpr h2
  · rintro ⟨h1, hxX⟩
    refine (mem_pull ψ _ hxX).mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, (ψ ⟨x, hxX⟩).2⟩)
    intro e he
    obtain ⟨y, hyX, hye⟩ := exists_psi_eq ψ (hE he)
    have hy : y ∈ pull ψ E' := (mem_pull ψ _ hyX).mpr (by rw [hye]; exact he)
    have h2 := Subgroup.mem_centralizer_iff.mp h1 y hy
    have h3 := (pe_comm_iff ψ hyX hxX).mp h2
    rw [← hye]
    exact h3

theorem pull_normalizer_inf (ψ : ↥X ≃* ↥X') {E' : Subgroup Gs} (hE : E' ≤ X') :
    pull ψ (normalizer (E' : Set Gs) ⊓ X') = normalizer ((pull ψ E' : Subgroup G) : Set G) ⊓ X := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · intro hx
    have hxX : x ∈ X := pull_le ψ _ hx
    have h := Subgroup.mem_inf.mp ((mem_pull ψ _ hxX).mp hx)
    exact ⟨(mem_normalizer_pull ψ hE hxX).mpr h.1, hxX⟩
  · rintro ⟨h1, hxX⟩
    exact (mem_pull ψ _ hxX).mpr (Subgroup.mem_inf.mpr ⟨(mem_normalizer_pull ψ hE hxX).mp h1, (ψ ⟨x, hxX⟩).2⟩)

theorem pull_centralizer_singleton (ψ : ↥X ≃* ↥X') {t : G} (ht : t ∈ X) {t' : Gs}
    (h : pe ψ t ht = t') :
    pull ψ (centralizer ({t'} : Set Gs)) = centralizer ({t} : Set G) ⊓ X := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · intro hx
    have hxX : x ∈ X := pull_le ψ _ hx
    have h1 := (mem_pull ψ _ hxX).mp hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hxX⟩
    have h2 : pe ψ x hxX * pe ψ t ht = pe ψ t ht * pe ψ x hxX := by
      rw [h]; exact Subgroup.mem_centralizer_singleton_iff.mp h1
    exact (pe_comm_iff ψ hxX ht).mpr h2
  · rintro ⟨h1, hxX⟩
    refine (mem_pull ψ _ hxX).mpr (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    have h2 := (pe_comm_iff ψ hxX ht).mp (Subgroup.mem_centralizer_singleton_iff.mp h1)
    rw [h] at h2
    exact h2

theorem pull_bot (ψ : ↥X ≃* ↥X') : pull ψ (⊥ : Subgroup Gs) = ⊥ := by
  ext x
  rw [Subgroup.mem_bot]
  constructor
  · intro hx
    have hxX : x ∈ X := pull_le ψ _ hx
    have h1 := (mem_pull ψ _ hxX).mp hx
    rw [Subgroup.mem_bot] at h1
    have : pe ψ x hxX = pe ψ 1 X.one_mem := by
      rw [show pe ψ 1 X.one_mem = 1 from psi_one ψ]; exact h1
    exact (pe_eq_iff ψ hxX X.one_mem).mp this
  · rintro rfl
    exact (mem_pull ψ _ X.one_mem).mpr (Subgroup.mem_bot.mpr (psi_one ψ))

theorem pe_pow (ψ : ↥X ≃* ↥X') {x : G} (hx : x ∈ X) (n : ℕ) :
    pe ψ (x ^ n) (X.pow_mem hx n) = (pe ψ x hx) ^ n := by
  have : (⟨x ^ n, X.pow_mem hx n⟩ : ↥X) = (⟨x, hx⟩ : ↥X) ^ n := rfl
  show ((ψ ⟨x ^ n, X.pow_mem hx n⟩ : ↥X') : Gs) = _
  rw [this, map_pow]
  rfl

theorem pe_one (ψ : ↥X ≃* ↥X') : pe ψ 1 X.one_mem = 1 := psi_one ψ

theorem pull_sup₃ (ψ : ↥X ≃* ↥X') {A B C : Subgroup Gs} (hA : A ≤ X') (hB : B ≤ X') (hC : C ≤ X') :
    pull ψ (A ⊔ B ⊔ C) = pull ψ A ⊔ pull ψ B ⊔ pull ψ C := by
  rw [pull_sup ψ (sup_le hA hB) hC, pull_sup ψ hA hB]

end Toolkit

section Torus

variable {G : Type} [Group G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem cjL_le_of_mem {g : Gs} {X' : Subgroup Gs} (hg : g ∈ X') {E : Subgroup Gs} (hE : E ≤ X') :
    cjL g E ≤ X' := by
  intro x hx
  have h1 : g⁻¹ * x * g ∈ E := mem_cjL.mp hx
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ X' := X'.mul_mem (X'.mul_mem hg (hE h1)) (X'.inv_mem hg)
  simpa [mul_assoc] using h2

theorem ModelPic.torus_of_five66W (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    {H : Subgroup G} {w₁ : G} (b66 : Five66W z t u K₁ K₂ H w₁) (hw₁C : w₁ ∈ Cz z) :
    IsTorus z' u' K₁' K₂' (push ψ H) ∧ pe ψ w₁ hw₁C ∈ K₁' ∧ pe ψ w₁ hw₁C * pe ψ w₁ hw₁C = z' ∧
      pe ψ w₁ hw₁C * u' * (pe ψ w₁ hw₁C)⁻¹ = u' * z' := by
  have hzC : z ∈ Cz z := mem_Cz_self z
  have hHle : H ≤ Cz z := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr (b66.H_cent h hh).1
  have hH'X : push ψ H ≤ Cz z' := push_le ψ H
  have hpullH : pull ψ (push ψ H) = H := pull_push ψ hHle
  have hmemH : ∀ y (hy : y ∈ Cz z'), y ∈ push ψ H ↔ ((ψ.symm ⟨y, hy⟩ : ↥(Cz z)) : G) ∈ H :=
    fun y hy => mem_push ψ H hy
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro y hy
    have hyC : y ∈ Cz z' := hH'X hy
    have hx := (hmemH y hyC).mp hy
    set x : G := ((ψ.symm ⟨y, hyC⟩ : ↥(Cz z)) : G) with hxdef
    have hxC : x ∈ Cz z := (ψ.symm ⟨y, hyC⟩).2
    have hpx : pe ψ x hxC = y := by
      show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) = y
      have : ψ ⟨x, hxC⟩ = ⟨y, hyC⟩ := by
        have h := ψ.apply_symm_apply ⟨y, hyC⟩
        exact h
      exact congrArg Subtype.val this
    obtain ⟨c1, c2⟩ := b66.H_cent x hx
    refine mem_PP.mpr ⟨?_, ?_⟩
    · have h := (pe_comm_iff ψ hxC hzC).mp c1
      have h' : ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) =
          ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) := h
      rw [pic.psi_z] at h'
      rwa [show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) = y from hpx] at h'
    · have h := (pe_comm_iff ψ hxC hu).mp c2
      have h' : ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) =
          ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) := h
      rw [pic.psi_u] at h'
      rwa [show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) = y from hpx] at h'
  ·
    exact ⟨((pullEquiv ψ hH'X).symm.trans (MulEquiv.subgroupCongr hpullH)).trans b66.H_iso.some⟩
  ·
    intro y hy
    have hyC : y ∈ Cz z' := hH'X hy
    have hx := (hmemH y hyC).mp hy
    set x : G := ((ψ.symm ⟨y, hyC⟩ : ↥(Cz z)) : G) with hxdef
    have hxC : x ∈ Cz z := (ψ.symm ⟨y, hyC⟩).2
    have hpx : pe ψ x hxC = y := by
      show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) = y
      have : ψ ⟨x, hxC⟩ = ⟨y, hyC⟩ := ψ.apply_symm_apply ⟨y, hyC⟩
      exact congrArg Subtype.val this
    obtain ⟨n1, n2⟩ := b66.H_normK x hx
    have e1 : pull ψ (cjL y K₁') = pull ψ K₁' := by
      rw [← hpx, ← pull_cjL ψ hxC, pic.K₁_eq]; exact n1
    have e2 : pull ψ (cjL y K₂') = pull ψ K₂' := by
      rw [← hpx, ← pull_cjL ψ hxC, pic.K₂_eq]; exact n2
    exact ⟨pull_inj ψ (cjL_le_of_mem hyC pic.K₁'_le) pic.K₁'_le e1,
      pull_inj ψ (cjL_le_of_mem hyC pic.K₂'_le) pic.K₂'_le e2⟩
  · have h : w₁ ∈ pull ψ K₁' := by rw [pic.K₁_eq]; exact b66.w₁_mem
    exact (mem_pull ψ K₁' hw₁C).mp h
  · have h : pe ψ (w₁ * w₁) ((Cz z).mul_mem hw₁C hw₁C) = pe ψ z hzC :=
      (pe_eq_iff ψ _ hzC).mpr (by rw [← pow_two]; exact b66.w₁_sq)
    rw [pe_mul ψ hw₁C hw₁C] at h
    exact h.trans pic.psi_z
  · have h : pe ψ (w₁ * u * w₁⁻¹)
        ((Cz z).mul_mem ((Cz z).mul_mem hw₁C hu) ((Cz z).inv_mem hw₁C)) =
        pe ψ (u * z) ((Cz z).mul_mem hu hzC) :=
      (pe_eq_iff ψ _ _).mpr b66.w₁_u
    rw [pe_conj ψ hw₁C hu, pe_mul ψ hu hzC] at h
    have h1 : pe ψ u hu = u' := pic.psi_u
    have h2 : pe ψ z hzC = z' := pic.psi_z
    rw [h1, h2] at h
    exact h

end Torus

section Core82

variable {G : Type} [Group G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem push_mono' {X : Subgroup G} {X' : Subgroup Gs} (ψ : ↥X ≃* ↥X') {A B : Subgroup G} (h : A ≤ B) :
    push ψ A ≤ push ψ B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono X h)

theorem push_pull' {X : Subgroup G} {X' : Subgroup Gs} (ψ : ↥X ≃* ↥X') {E : Subgroup Gs}
    (hE : E ≤ X') : push ψ (pull ψ E) = E := by
  apply pull_inj ψ (push_le ψ _) hE
  exact pull_push ψ (pull_le ψ E)

theorem pe_mem_push {X : Subgroup G} {X' : Subgroup Gs} (ψ : ↥X ≃* ↥X') {A : Subgroup G} {x : G}
    (hxA : x ∈ A) (hx : x ∈ X) : pe ψ x hx ∈ push ψ A := by
  rw [mem_push ψ A (ψ ⟨x, hx⟩).2]
  simpa using hxA

theorem exists_pe_of_mem_push {X : Subgroup G} {X' : Subgroup Gs} (ψ : ↥X ≃* ↥X') {A : Subgroup G}
    {y : Gs} (hy : y ∈ push ψ A) : ∃ (x : G) (hx : x ∈ X), x ∈ A ∧ pe ψ x hx = y := by
  have hyX : y ∈ X' := push_le ψ A hy
  refine ⟨((ψ.symm ⟨y, hyX⟩ : ↥X) : G), (ψ.symm ⟨y, hyX⟩).2, (mem_push ψ A hyX).mp hy, ?_⟩
  show ((ψ ⟨((ψ.symm ⟨y, hyX⟩ : ↥X) : G), (ψ.symm ⟨y, hyX⟩).2⟩ : ↥X') : Gs) = y
  have : ψ ⟨((ψ.symm ⟨y, hyX⟩ : ↥X) : G), (ψ.symm ⟨y, hyX⟩).2⟩ = ⟨y, hyX⟩ :=
    ψ.apply_symm_apply _
  exact congrArg Subtype.val this

theorem push_hinv {X : Subgroup G} {X' : Subgroup Gs} (ψ : ↥X ≃* ↥X') {H A : Subgroup G}
    (hA : A ≤ X) (h : ∀ x ∈ H, cjL x A = A) : ∀ y ∈ push ψ H, cjL y (push ψ A) = push ψ A := by
  intro y hy
  obtain ⟨x, hxX, hxH, rfl⟩ := exists_pe_of_mem_push ψ hy
  have e1 : pull ψ (cjL (pe ψ x hxX) (push ψ A)) = cjL x A := by
    rw [← pull_cjL ψ hxX, pull_push ψ hA]
  have e2 : pull ψ (push ψ A) = A := pull_push ψ hA
  apply pull_inj ψ (cjL_le_of_mem (ψ ⟨x, hxX⟩).2 (push_le ψ A)) (push_le ψ A)
  rw [e1, e2]
  exact h x hxH

end Core82

section Five82Core

variable {G : Type} [Group G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem card_of_isSylowIn_five [Finite G] {P M : Subgroup G} (h : IsSylowIn 5 P M)
    (hM : Nat.card ↥M = 28800) : Nat.card ↥P = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hPM, hP5, hidx⟩ := h
  obtain ⟨n, hn⟩ := hP5.exists_card_eq
  have h1 := Subgroup.card_mul_index (P.subgroupOf M)
  have h2 : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  rw [h2, hn, hM] at h1
  have hn3 : n ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 5 ^ 3 ∣ 5 ^ n := pow_dvd_pow 5 hlt
    have h3 : 5 ^ 3 ∣ 28800 := by rw [← h1]; exact Dvd.dvd.mul_right this _
    omega
  rw [hn]
  interval_cases n
  · exfalso; apply hidx; omega
  · exfalso; apply hidx; omega
  · rfl

theorem isSylowIn_five_of_card {P M : Subgroup G} (hPM : P ≤ M) (hP : Nat.card ↥P = 25)
    (hM : Nat.card ↥M = 28800) : IsSylowIn 5 P M := by
  refine ⟨hPM, IsPGroup.of_card (n := 2) (by rw [hP]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index (P.subgroupOf M)
  have h2 : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  rw [h2, hP, hM] at h1
  omega

end Five82Core

section Five82Core2

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem ModelPic.five82_core (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (hK₁ : Nat.card ↥K₁ = 120) (hC : Nat.card ↥(Cz z) = 28800)
    {H : Subgroup G} {w₁ : G} (b66 : Five66W z t u K₁ K₂ H w₁) :
    ∃ X₁ : Subgroup G, X₁ ≤ K₁ ∧ IsSylowIn 5 X₁ K₁ ∧ Nat.card ↥X₁ = 5 ∧
      (∀ h ∈ H, cjL h X₁ = X₁) ∧ Subgroup.closure ((X₁ : Set G) ∪ {w₁}) = K₁ ∧
      (∀ x ∈ X₁, u * x * u⁻¹ = x⁻¹) ∧
      normalizer ((XB t X₁ : Subgroup G) : Set G) ⊓ Cz z = XB t X₁ ⊔ K₁ ⊔ H ∧
      centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ Cz z = XB t X₁ ⊔ K₁ ∧
      normalizer ((XX t X₁ : Subgroup G) : Set G) ⊓ Cz z = XX t X₁ ⊔ H ⊔ zpowers t ∧
      (∀ R : Subgroup G, IsSylowIn 5 R (Cz z) → (∀ h ∈ H, cjL h R = R) →
        ∃ w ∈ zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹), R = cjL w (XX t X₁)) ∧
      (∀ A : Subgroup G, A ≤ XX t X₁ → Nat.card ↥A = 5 → (∀ h ∈ H, cjL h A = A) →
        A = X₁ ∨ A = XB t X₁) ∧
      Nat.card ↥(XZ t X₁) = 5 := by
  classical
  have hzC : z ∈ Cz z := mem_Cz_self z
  have hK₁le : K₁ ≤ Cz z := by rw [← pic.K₁_eq]; exact pull_le ψ K₁'
  have hw₁C : w₁ ∈ Cz z := hK₁le b66.w₁_mem
  have hHle : H ≤ Cz z := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr (b66.H_cent h hh).1
  obtain ⟨hT, hw'K, hw'sq, hw'u⟩ := pic.torus_of_five66W b66 hw₁C
  have hH'X : push ψ H ≤ Cz z' := push_le ψ H
  have hpullH : pull ψ (push ψ H) = H := pull_push ψ hHle
  obtain ⟨X₁', hX1le, hX1c, hX1H, hX1gen, hX1u, hNC2, hCC2, hNCX, hsyl, hinv, hX0c⟩ :=
    pic.facts.X1_exists (push ψ H) (pe ψ w₁ hw₁C) hT ⟨hw'K, hw'sq, hw'u⟩
  have hX1'C : X₁' ≤ Cz z' := hX1le.trans pic.K₁'_le
  have ht'C : t' ∈ Cz z' := by rw [← pic.psi_t]; exact (ψ ⟨t, ht⟩).2
  have hXB'C : XB t' X₁' ≤ Cz z' := cjL_le_of_mem ht'C hX1'C
  have hXX'C : XX t' X₁' ≤ Cz z' := sup_le hX1'C hXB'C
  have hXB : XB t (pull ψ X₁') = pull ψ (XB t' X₁') := by
    show cjL t (pull ψ X₁') = pull ψ (cjL t' X₁')
    have hpt : pe ψ t ht = t' := pic.psi_t
    rw [pull_cjL ψ ht, hpt]
  have hXX : XX t (pull ψ X₁') = pull ψ (XX t' X₁') := by
    show pull ψ X₁' ⊔ XB t (pull ψ X₁') = pull ψ (X₁' ⊔ XB t' X₁')
    rw [hXB, pull_sup ψ hX1'C hXB'C]
  have hcardX : Nat.card ↥(pull ψ X₁') = 5 := (card_pull ψ hX1'C).trans hX1c
  have hle : pull ψ X₁' ≤ K₁ := by rw [← pic.K₁_eq]; exact pull_mono ψ hX1le
  refine ⟨pull ψ X₁', hle, ?_, hcardX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨hle, IsPGroup.of_card (n := 1) (by rw [hcardX]; norm_num), ?_⟩
    have h1 := Subgroup.card_mul_index ((pull ψ X₁').subgroupOf K₁)
    have h2 : Nat.card ↥((pull ψ X₁').subgroupOf K₁) = 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardX]
    rw [h2, hK₁] at h1
    omega
  ·
    intro h hh
    have hhC : h ∈ Cz z := hHle hh
    rw [pull_cjL ψ hhC]
    rw [hX1H _ (pe_mem_push ψ hh hhC)]
  ·
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hle hx
      · rw [Set.mem_singleton_iff.mp hx]; exact b66.w₁_mem
    · set M : Subgroup G := Subgroup.closure ((pull ψ X₁' : Set G) ∪ {w₁}) with hM
      have hMX : M ≤ Cz z := by
        rw [hM, Subgroup.closure_le]
        rintro x (hx | hx)
        · exact pull_le ψ _ hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hw₁C
      have hK' : K₁' ≤ push ψ M := by
        rw [← hX1gen, Subgroup.closure_le]
        rintro x' (hx' | hx')
        · have hx'C : x' ∈ Cz z' := hX1'C hx'
          show x' ∈ push ψ M
          rw [mem_push ψ M hx'C]
          have : ((ψ.symm ⟨x', hx'C⟩ : ↥(Cz z)) : G) ∈ pull ψ X₁' := by
            rw [mem_pull ψ _ (ψ.symm ⟨x', hx'C⟩).2]
            simpa using hx'
          exact Subgroup.subset_closure (Or.inl this)
        · rw [Set.mem_singleton_iff.mp hx']
          have hw'C : pe ψ w₁ hw₁C ∈ Cz z' := (ψ ⟨w₁, hw₁C⟩).2
          show pe ψ w₁ hw₁C ∈ push ψ M
          rw [mem_push ψ M hw'C]
          have : ((ψ.symm ⟨pe ψ w₁ hw₁C, hw'C⟩ : ↥(Cz z)) : G) = w₁ := by
            have : ψ.symm ⟨pe ψ w₁ hw₁C, hw'C⟩ = ⟨w₁, hw₁C⟩ := by
              rw [MulEquiv.symm_apply_eq]
            rw [this]
          rw [this]
          exact Subgroup.subset_closure (Or.inr rfl)
      calc K₁ = pull ψ K₁' := pic.K₁_eq.symm
        _ ≤ pull ψ (push ψ M) := pull_mono ψ hK'
        _ = M := pull_push ψ hMX
  ·
    intro x hx
    have hxC : x ∈ Cz z := pull_le ψ _ hx
    have hx' := (mem_pull ψ _ hxC).mp hx
    have hxinv : x⁻¹ ∈ Cz z := (Cz z).inv_mem hxC
    refine (pe_eq_iff ψ ((Cz z).mul_mem ((Cz z).mul_mem hu hxC) ((Cz z).inv_mem hu)) hxinv).mp ?_
    rw [pe_conj ψ hu hxC, pe_inv ψ hxC]
    have h1 : pe ψ u hu = u' := pic.psi_u
    rw [h1]
    exact hX1u _ hx'
  ·
    rw [hXB, ← pull_normalizer_inf ψ hXB'C, hNC2, pull_sup₃ ψ hXB'C pic.K₁'_le hH'X, pic.K₁_eq,
      hpullH]
  · rw [hXB, ← pull_centralizer_inf ψ hXB'C, hCC2, pull_sup ψ hXB'C pic.K₁'_le, pic.K₁_eq]
  · have hzt : zpowers t' ≤ Cz z' := Subgroup.zpowers_le.mpr ht'C
    rw [hXX, ← pull_normalizer_inf ψ hXX'C, hNCX, pull_sup₃ ψ hXX'C hH'X hzt, hpullH,
      pull_zpowers ψ ht pic.psi_t]
  · intro R hR hRH
    have hRC : R ≤ Cz z := hR.1
    have hpullR : pull ψ (push ψ R) = R := pull_push ψ hRC
    have hcR : Nat.card ↥R = 25 := card_of_isSylowIn_five hR hC
    have hcR' : Nat.card ↥(push ψ R) = 25 :=
      (card_pull ψ (push_le ψ R)).symm.trans (by rw [hpullR]; exact hcR)
    have hCz'card : Nat.card ↥(Cz z') = 28800 := by
      rw [← hC]; exact (Nat.card_congr ψ.toEquiv).symm
    have hR'syl : IsSylowIn 5 (push ψ R) (Cz z') :=
      isSylowIn_five_of_card (push_le ψ R) hcR' hCz'card
    obtain ⟨w, hwW, hRw⟩ := hsyl (push ψ R) hR'syl (push_hinv ψ hRC hRH)
    have hw'C : pe ψ w₁ hw₁C ∈ Cz z' := (ψ ⟨w₁, hw₁C⟩).2
    have hw2'C : t' * pe ψ w₁ hw₁C * t'⁻¹ ∈ Cz z' :=
      (Cz z').mul_mem ((Cz z').mul_mem ht'C hw'C) ((Cz z').inv_mem ht'C)
    have hW'C : zpowers (pe ψ w₁ hw₁C) ⊔ zpowers (t' * pe ψ w₁ hw₁C * t'⁻¹) ≤ Cz z' :=
      sup_le (Subgroup.zpowers_le.mpr hw'C) (Subgroup.zpowers_le.mpr hw2'C)
    obtain ⟨w₀, hw₀C, hψw₀⟩ := exists_psi_eq ψ (hW'C hwW)
    have hwtC : t * w₁ * t⁻¹ ∈ Cz z := (Cz z).mul_mem ((Cz z).mul_mem ht hw₁C) ((Cz z).inv_mem ht)
    have hpe2 : pe ψ (t * w₁ * t⁻¹) hwtC = t' * pe ψ w₁ hw₁C * t'⁻¹ := by
      have h := pe_conj ψ ht hw₁C
      have h1 : pe ψ t ht = t' := pic.psi_t
      rw [h1] at h
      exact h
    have hpullW : pull ψ (zpowers (pe ψ w₁ hw₁C) ⊔ zpowers (t' * pe ψ w₁ hw₁C * t'⁻¹)) =
        zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹) := by
      rw [pull_sup ψ (Subgroup.zpowers_le.mpr hw'C) (Subgroup.zpowers_le.mpr hw2'C),
        pull_zpowers ψ hw₁C rfl, pull_zpowers ψ hwtC hpe2]
    refine ⟨w₀, ?_, ?_⟩
    · rw [← hpullW]
      refine (mem_pull ψ _ hw₀C).mpr ?_
      have h0 : pe ψ w₀ hw₀C = w := hψw₀
      show pe ψ w₀ hw₀C ∈ _
      rw [h0]; exact hwW
    · rw [hXX, pull_cjL ψ hw₀C]
      have h0 : pe ψ w₀ hw₀C = w := hψw₀
      rw [h0, ← hRw, hpullR]
  · intro A hA hAc hAH
    have hAC : A ≤ Cz z := hA.trans (by rw [hXX]; exact pull_le ψ _)
    have hpullA : pull ψ (push ψ A) = A := pull_push ψ hAC
    have hA'le : push ψ A ≤ XX t' X₁' := by
      have := push_mono' ψ hA
      rwa [hXX, push_pull' ψ hXX'C] at this
    have hA'c : Nat.card ↥(push ψ A) = 5 :=
      (card_pull ψ (push_le ψ A)).symm.trans (by rw [hpullA]; exact hAc)
    rcases hinv (push ψ A) hA'le hA'c (push_hinv ψ hAC hAH) with h | h
    · left; rw [← hpullA, h]
    · right; rw [hXB, ← hpullA, h]
  ·
    have hZ : XZ t (pull ψ X₁') = pull ψ (XZ t' X₁') := by
      show XX t (pull ψ X₁') ⊓ centralizer ({t} : Set G) =
        pull ψ (XX t' X₁' ⊓ centralizer ({t'} : Set Gs))
      rw [pull_inf, hXX, pull_centralizer_singleton ψ ht pic.psi_t]
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, pull_le ψ _ h1⟩
      · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    rw [hZ]
    exact (card_pull ψ (inf_le_left.trans hXX'C)).trans hX0c

end Five82Core2

end CFSG.GH74.GLS.LU.Local.Five
