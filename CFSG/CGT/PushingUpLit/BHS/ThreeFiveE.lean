module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveD

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman CFSG.RankThree.PartOne CFSG.Open
  CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

theorem sec_sq_eq_one' (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) (s : Sec W U) : s ^ 2 = 1 := by
  induction s using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow]
    have : (w ^ 2 : ↥W) = 1 := Subtype.ext (by simpa using hV (w : V))
    rw [this]
    rfl

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

theorem comm_sq_A : (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1 := by
  refine ⟨fun a ha b hb => h.faithful ?_, fun a ha => h.faithful ?_⟩
  · rw [map_mul, map_mul]
    exact h.elemAb.1 _ (Subgroup.mem_map_of_mem ρ ha) _ (Subgroup.mem_map_of_mem ρ hb)
  · rw [map_pow, map_one]
    exact h.elemAb.2 _ (Subgroup.mem_map_of_mem ρ ha)

theorem wt_le [Finite V] {B : Subgroup (MulAut V)} (hB : B ≤ A.map ρ) :
    Nat.card B * Nat.card (fixV B) ≤ Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ)) := by
  by_cases hB0 : B = ⊥
  · subst hB0
    have := B1.card_bot_mul_card_fixV (V := V)
    rw [this]
    exact h.card_le
  · by_cases hBA : B = A.map ρ
    · subst hBA
      exact le_rfl
    · exact (h.lt_wt B hB hB0 hBA).le

theorem map_secF_ne_bot [Finite Γ] : A.map (secF ρ T) ≠ ⊥ := by
  intro hA
  apply h.not_le_cenW
  intro a ha
  have h1 : secF ρ T a ∈ A.map (secF ρ T) := Subgroup.mem_map_of_mem _ ha
  rw [hA, Subgroup.mem_bot] at h1
  exact h.ker_secF_le.1 ⟨(MonoidHom.mem_ker).2 h1, Subgroup.mem_top a⟩

theorem isElemAbelian2_map_secF : IsElemAbelian2 (A.map (secF ρ T)) := by
  have hA := h.comm_sq_A
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.2 x hx, map_one]

theorem isQuadratic_map_secF [Finite V] : IsQuadratic (A.map (secF ρ T)) := by
  have hq := h.quadratic
  show commV _ ≤ fixV _
  rw [G6.commV_le_iff]
  rintro _ ⟨a, ha, rfl⟩ v
  induction v using QuotientGroup.induction_on with
  | H w =>
    have hc : ρ a w * (w : V)⁻¹ ∈ commV (A.map ρ) :=
      G6.mem_commV_of_mem (Subgroup.mem_map_of_mem ρ ha) _
    set c : ↥(wMod ρ T) := ⟨ρ a w * (w : V)⁻¹, Subgroup.mul_mem _ (wMod_inv ρ T a w.2)
      (Subgroup.inv_mem _ w.2)⟩ with hcdef
    have h1 : secF ρ T a (QuotientGroup.mk w) * (QuotientGroup.mk w)⁻¹ = QuotientGroup.mk c := by
      rw [secF_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
    rw [h1]
    rintro _ ⟨a', ha', rfl⟩
    rw [secF_mk]
    congr 1
    exact Subtype.ext (hq hc _ (Subgroup.mem_map_of_mem ρ ha'))

theorem sup_zpowers_map_secF {g : MulAut (Sec (wMod ρ T) (fixV ρ.range))}
    (hg : g ∈ (⊤ : Subgroup Γ).map (secF ρ T)) (hgM : g ∉ M.map (secF ρ T)) :
    A.map (secF ρ T) ⊔ Subgroup.zpowers g = (⊤ : Subgroup Γ).map (secF ρ T) := by
  obtain ⟨x, -, rfl⟩ := hg
  have hx : x ∉ M := fun hxM => hgM (Subgroup.mem_map_of_mem _ hxM)
  refine le_antisymm (sup_le (Subgroup.map_mono le_top) ?_) ?_
  · exact (Subgroup.zpowers_le).2 (Subgroup.mem_map_of_mem _ (Subgroup.mem_top x))
  · have hgen := congrArg (Subgroup.map (secF ρ T)) (h.gen x hx)
    rw [Subgroup.map_sup] at hgen
    rw [← hgen]
    refine sup_le le_sup_left ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have : secF ρ T ((MulAut.conj x).toMonoidHom a) =
        secF ρ T x * secF ρ T a * (secF ρ T x)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [this]
    have hz : secF ρ T x ∈ A.map (secF ρ T) ⊔ Subgroup.zpowers (secF ρ T x) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ ha))) (Subgroup.inv_mem _ hz)

theorem fixV_map_secF [Finite V] : fixV ((⊤ : Subgroup Γ).map (secF ρ T)) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  induction s using QuotientGroup.induction_on with
  | H w =>
    have hΓ : ∀ g : Γ, ρ g (w : V) * (w : V)⁻¹ ∈ fixV ρ.range := by
      intro g
      have h1 := mem_fixV.1 hs (secF ρ T g) (Subgroup.mem_map_of_mem _ (Subgroup.mem_top g))
      rw [secF_mk] at h1
      have h2 := (mk_eq_mk_iff (U := (fixV ρ.range).subgroupOf (wMod ρ T)) _ _).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    have := h.mem_fixV_range_of_mod w.2 hΓ
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact this

omit h in
theorem fixV_range_le_fixV_map (ρ : Γ →* MulAut V) (X : Subgroup Γ) :
    fixV ρ.range ≤ fixV (X.map ρ) := fun v hv x hx => by
  obtain ⟨a, -, rfl⟩ := hx
  exact hv _ ⟨a, rfl⟩

omit h in
theorem fixV_range_le_wMod (ρ : Γ →* MulAut V) (T : Subgroup Γ) :
    fixV ρ.range ≤ wMod ρ T := (fixV_range_le ρ T).trans (fixV_le_wMod ρ T)

omit h in
theorem card_wMod_inf_le [Finite V] [Finite Γ] :
    Nat.card ↥(wMod ρ T ⊓ fixV (A.map ρ)) ≤
      Nat.card (fixV (A.map (secF ρ T))) * Nat.card (fixV ρ.range) := by
  have hAW : A.map ρ ≤ stabSub (wMod ρ T) := by
    rintro _ ⟨a, -, rfl⟩
    exact stab_wMod ρ T a
  have h1 : Nat.card ↥(wMod ρ T ⊓ fixV (A.map ρ)) ≤
      Nat.card (fixV (autSec (A.map ρ) (wMod ρ T) (fixV ρ.range))) *
        Nat.card ↥(fixV ρ.range ⊓ fixV (A.map ρ)) :=
    card_inf_fixV_le_autSec (A := A.map ρ) (fixV_range_le_wMod ρ T) hAW
  rw [autSec_map_eq ρ _ _ (stab_wMod ρ T) (stab_fixV_range ρ) A,
    inf_eq_left.2 (fixV_range_le_fixV_map ρ A)] at h1
  exact h1

theorem sup_le_fixV_ker [Finite Γ] :
    wMod ρ T ⊔ fixV (A.map ρ) ≤ fixV ((A ⊓ (secF ρ T).ker).map ρ) := by
  refine sup_le (fun w hw x hx => ?_) (fun v hv x hx => hv x ?_)
  · obtain ⟨a, ha, rfl⟩ := hx
    exact mem_cenMod.1 (h.ker_secF_le.1 ⟨ha.2, Subgroup.mem_top a⟩) w hw
  · obtain ⟨a, ha, rfl⟩ := hx
    exact Subgroup.mem_map_of_mem ρ ha.1

theorem card_ker_mul_le [Finite V] [Finite Γ] :
    Nat.card ↥(A ⊓ (secF ρ T).ker) * Nat.card (wMod ρ T) ≤
      Nat.card A * Nat.card ↥(wMod ρ T ⊓ fixV (A.map ρ)) := by
  set W := wMod ρ T with hW
  set F := fixV (A.map ρ) with hF
  set K := A ⊓ (secF ρ T).ker with hK
  have hKle : K.map ρ ≤ A.map ρ := Subgroup.map_mono inf_le_left
  have hwt := h.wt_le hKle
  have hcardsup : Nat.card ↥(W ⊔ F) ≤ Nat.card (fixV (K.map ρ)) :=
    Subgroup.card_le_of_le h.sup_le_fixV_ker
  have hKcard : Nat.card (K.map ρ) = Nat.card K := Subgroup.card_map_of_injective h.faithful
  have hAcard : Nat.card (A.map ρ) = Nat.card A := Subgroup.card_map_of_injective h.faithful
  rw [hKcard, hAcard] at hwt
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have h1 : Nat.card K * Nat.card ↥(W ⊔ F) ≤ Nat.card A * Nat.card F :=
    (Nat.mul_le_mul_left _ hcardsup).trans hwt
  have h2 : (Nat.card K * Nat.card W) * Nat.card F ≤
      (Nat.card A * Nat.card ↥(W ⊓ F)) * Nat.card F := by
    calc (Nat.card K * Nat.card W) * Nat.card F
        = Nat.card K * (Nat.card W * Nat.card F) := by ring
      _ = Nat.card K * (Nat.card ↥(W ⊔ F) * Nat.card ↥(W ⊓ F)) := by
          rw [card_sup_mul_card_inf W F]
      _ = (Nat.card K * Nat.card ↥(W ⊔ F)) * Nat.card ↥(W ⊓ F) := by ring
      _ ≤ (Nat.card A * Nat.card F) * Nat.card ↥(W ⊓ F) := Nat.mul_le_mul_right _ h1
      _ = (Nat.card A * Nat.card ↥(W ⊓ F)) * Nat.card F := by ring
  exact Nat.le_of_mul_le_mul_right h2 hFpos

theorem card_le_map_secF [Finite V] [Finite Γ] :
    Nat.card (Sec (wMod ρ T) (fixV ρ.range)) ≤
      Nat.card (A.map (secF ρ T)) * Nat.card (fixV (A.map (secF ρ T))) := by
  set W := wMod ρ T with hW
  set Y := fixV ρ.range with hY
  set f := secF ρ T with hf
  have hcardW : Nat.card (Sec W Y) * Nat.card Y = Nat.card W :=
    card_sec_mul (fixV_range_le_wMod ρ T)
  have hC := card_wMod_inf_le (ρ := ρ) (T := T) (A := A)
  have hkey := h.card_ker_mul_le
  have hA : Nat.card A = Nat.card (A.map f) * Nat.card ↥(A ⊓ f.ker) :=
    (B1More.card_map_mul_card_inf_ker A f).symm
  have ha₀pos : 0 < Nat.card ↥(A ⊓ f.ker) := Nat.card_pos
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have h3 : Nat.card ↥(A ⊓ f.ker) * (Nat.card (Sec W Y) * Nat.card Y) ≤
      Nat.card ↥(A ⊓ f.ker) * (Nat.card (A.map f) * Nat.card (fixV (A.map f)) * Nat.card Y) := by
    rw [hcardW]
    calc Nat.card ↥(A ⊓ f.ker) * Nat.card W
        ≤ Nat.card A * Nat.card ↥(W ⊓ fixV (A.map ρ)) := hkey
      _ ≤ Nat.card A * (Nat.card (fixV (A.map f)) * Nat.card Y) := Nat.mul_le_mul_left _ hC
      _ = Nat.card ↥(A ⊓ f.ker) *
            (Nat.card (A.map f) * Nat.card (fixV (A.map f)) * Nat.card Y) := by
          rw [hA]; ring
  have h4 := Nat.le_of_mul_le_mul_left h3 ha₀pos
  exact Nat.le_of_mul_le_mul_right h4 hYpos

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
