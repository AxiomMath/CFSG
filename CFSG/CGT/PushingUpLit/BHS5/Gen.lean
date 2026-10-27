module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V]

theorem fixV_anti {X Y : Subgroup (MulAut V)} (h : Y ≤ X) : fixV X ≤ fixV Y :=
  fun _ hv y hy => hv y (h hy)

theorem le_iSup_mem {D : Set (Subgroup (MulAut V))} {A : Subgroup (MulAut V)} (hA : A ∈ D) :
    A ≤ ⨆ B ∈ D, B :=
  le_iSup₂ (f := fun B (_ : B ∈ D) => B) A hA

theorem conjSub_of_mem {G : Type*} [Group G] {t : G} {M : Subgroup G} (ht : t ∈ M) :
    conjSub t M = M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem ht hy) (M.inv_mem ht)
  · intro hx
    exact ⟨t⁻¹ * x * t, M.mul_mem (M.mul_mem (M.inv_mem ht) hx) ht, by simp [mul_assoc]⟩

section Gen

variable [Finite V] {P T M : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, g = h * k}
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * (k * h' * k⁻¹), H.mul_mem hh ?_, k * k', K.mul_mem hk hk', by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hK hk) h').1 hh'
        exact this
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, K.inv_mem hk, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hK (K.inv_mem hk)) h⁻¹).1 (H.inv_mem hh)
        simpa using this }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hg

omit [Finite V] in
theorem iSup_normalized (h : Hyp41 P D) :
    P ≤ Subgroup.normalizer ((⨆ A ∈ D, A : Subgroup (MulAut V)) : Set (MulAut V)) := by
  have key : ∀ g ∈ P, ∀ y ∈ (⨆ A ∈ D, A : Subgroup (MulAut V)),
      g * y * g⁻¹ ∈ (⨆ A ∈ D, A : Subgroup (MulAut V)) := by
    intro g hg y hy
    have hle : conjSub g (⨆ A ∈ D, A : Subgroup (MulAut V)) ≤ ⨆ A ∈ D, A := by
      rw [conjSub, Subgroup.map_iSup]
      refine iSup_le fun A => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hA => ?_
      exact le_iSup_mem (h.conj_mem A hA g hg)
    exact hle ⟨y, hy, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (P.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem hyp43_gen (h : Hyp43 P D T M) (hPT : P = (⨆ A ∈ D, A) ⊔ T) :
    Hyp43 (⨆ A ∈ D, A) D ((⨆ A ∈ D, A) ⊓ T) ((⨆ A ∈ D, A) ⊓ M) := by
  set P' : Subgroup (MulAut V) := ⨆ A ∈ D, A with hP'
  have hP'P : P' ≤ P := iSup₂_le fun A hA => h.le A hA
  have hnorm := iSup_normalized h.toHyp41
  have hdI : dInter D (P' ⊓ T) = dInter D T := by
    ext A
    simp only [dInter, Set.mem_ofPred_eq, le_inf_iff]
    exact ⟨fun ⟨hA, _, hAT⟩ => ⟨hA, hAT⟩, fun ⟨hA, hAT⟩ => ⟨hA, le_iSup_mem hA, hAT⟩⟩
  have hPN : P ≤ P' ⊔ T := hPT.le
  refine
    { toHyp42 :=
      { toHyp41 :=
        { le := fun A hA => le_iSup_mem hA
          ne_bot := h.ne_bot
          elemAb := h.elemAb
          conj_mem := fun A hA g hg => h.conj_mem A hA g (hP'P hg)
          quad := h.quad
          card_eq := h.card_eq
          fixV_eq := h.fixV_eq
          card_prod := h.card_prod }
        syl := FourTwoTools.isSylowOf_inf_of_le_normalizer h.syl hP'P hnorm
        le_M := inf_le_inf_left _ h.le_M
        M_le := inf_le_left
        ne_core := ?_
        normSet_le := ?_
        cen_le := ?_ }
      max := fun A hA X hX hXP => h.max A hA X hX (hXP.trans hP'P) }
  ·
    intro hD
    apply h.ne_core
    refine Set.Subset.antisymm (fun A hA => ?_) (fun A hA => hA.1)
    refine ⟨hA, fun g hg => ?_⟩
    have hTN : T ≤ Subgroup.normalizer (P' : Set (MulAut V)) := h.syl.1.trans hnorm
    obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_mem_sup hTN (hPT ▸ hg)
    have hcore : A ∈ dCore P' D (P' ⊓ M) := hD ▸ hA
    have h1 : A ≤ conjSub a (P' ⊓ M) := hcore.2 a ha
    rw [conjSub_mul, conjSub_of_mem (h.le_M ht)]
    exact h1.trans (Subgroup.map_mono inf_le_right)
  · intro g hg
    rw [hdI] at hg
    exact ⟨hg.1, h.normSet_le ⟨hP'P hg.1, hg.2⟩⟩
  · intro g hg
    exact ⟨hg.1, h.cen_le ⟨hP'P hg.1, fun u hu => hg.2 u (fixV_anti inf_le_right hu)⟩⟩

end Gen

end CFSG.CGT.PushingUpLit.BHS5
