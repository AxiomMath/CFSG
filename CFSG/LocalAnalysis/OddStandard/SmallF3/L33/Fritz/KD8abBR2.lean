module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBR2Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBCent

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem nfBits_gens : nfBits w₂ = [true, false, false, false, false, false, false, false] ∧
    nfBits u = [false, true, false, false, false, false, false, false] ∧
    nfBits w₁ = [false, false, true, false, false, false, false, false] ∧
    nfBits v = [false, false, false, true, false, false, false, false] ∧
    nfBits z = [false, false, false, false, true, false, false, false] ∧
    nfBits y = [false, false, false, false, false, true, false, false] ∧
    nfBits t = [false, false, false, false, false, false, true, false] ∧
    nfBits k = [false, false, false, false, false, false, false, true] := by decide +kernel

theorem applyMB_gens (f : List MB) (hf : f.length = 8) :
    gens.map (applyMB f) = f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := nfBits_gens
  match f, hf with
  | [a, b, c, d, e, f, g, h], _ =>
    simp [gens, applyMB, h1, h2, h3, h4, h5, h6, h7, h8, nfProd]

theorem bitsR1_k : bitsR1 k = [false, false, false, false, false, false, true] := by
  decide +kernel

theorem applyR1_k (f : List MB) (hf : f.length = 7) : applyR1 f k = f.getD 6 1 := by
  match f, hf with
  | [a, b, c, d, e, f, g], _ => simp [applyR1, bitsR1_k, nfProd]

theorem compR1_mem {f g : List MB} (hf : ∀ x ∈ f, inR1 x = true) :
    ∀ x ∈ compR1 f g, inR1 x = true := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact KD8abB.nfProd_mem (H := R1h) f _ hf

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
theorem ActsAs.conj {K : Subgroup X} {c g₀ h : X} (hc : ActsAs K c g₀)
    (hcK : c ∈ normalizer (K : Set X)) (hhK : h ∈ normalizer (K : Set X)) :
    ActsAs K (c * h * c⁻¹) (g₀ * h * g₀⁻¹) := by
  intro r hr
  have hr' := conj_inv_mem_of_mem_normalizer hcK hr
  have h1 := hc _ (conj_mem_of_mem_normalizer hhK hr')
  have h2 := hc _ hr'
  rw [show c * (c⁻¹ * r * c) * c⁻¹ = r by group] at h2
  calc c * h * c⁻¹ * r * (c * h * c⁻¹)⁻¹ = c * (h * (c⁻¹ * r * c) * h⁻¹) * c⁻¹ := by group
    _ = g₀ * (h * (c⁻¹ * r * c) * h⁻¹) * g₀⁻¹ := h1
    _ = g₀ * h * (g₀⁻¹ * (g₀ * (c⁻¹ * r * c) * g₀⁻¹) * g₀) * h⁻¹ * g₀⁻¹ := by group
    _ = g₀ * h * g₀⁻¹ * r * (g₀ * h * g₀⁻¹)⁻¹ := by rw [← h2]; group

omit [Finite X] in
theorem actsAs_conj_of {K : Subgroup X} {g₀ h h' : X} (hg₀ : g₀ ∈ normalizer (K : Set X))
    (hact : ActsAs K (g₀ * h) (h' * g₀)) : ActsAs K (g₀ * h * g₀⁻¹) h' := by
  intro r hr
  have := hact _ (conj_inv_mem_of_mem_normalizer hg₀ hr)
  calc g₀ * h * g₀⁻¹ * r * (g₀ * h * g₀⁻¹)⁻¹ = g₀ * h * (g₀⁻¹ * r * g₀) * (g₀ * h)⁻¹ := by group
    _ = h' * g₀ * (g₀⁻¹ * r * g₀) * (h' * g₀)⁻¹ := this
    _ = h' * r * h'⁻¹ := by group

omit [Finite X] in
theorem ActsAs.trans {K : Subgroup X} {g h h' : X} (h1 : ActsAs K g h) (h2 : ActsAs K h h') :
    ActsAs K g h' := fun r hr => (h1 r hr).trans (h2 r hr)

omit [Finite X] in
theorem ActsAs.nfProd {K : Subgroup X} :
    ∀ (L₁ L₂ : List X) (bs : List Bool), List.Forall₂ (ActsAs K) L₁ L₂ →
      (∀ h ∈ L₂, h ∈ normalizer (K : Set X)) → ActsAs K (Sec8.nfProd L₁ bs) (Sec8.nfProd L₂ bs)
  | [], [], _, _, _ => by simp [Sec8.nfProd, ActsAs.refl]
  | _ :: _, _ :: _, [], _, _ => by simp [Sec8.nfProd, ActsAs.refl]
  | g :: gs, h :: hs, b :: bs, hf, hn => by
    obtain ⟨hgh, hrest⟩ := List.forall₂_cons.mp hf
    have ih := ActsAs.nfProd gs hs bs hrest fun x hx => hn x (List.mem_cons_of_mem _ hx)
    simp only [Sec8.nfProd]
    have hnf : Sec8.nfProd hs bs ∈ normalizer (K : Set X) :=
      KD8abB.nfProd_mem hs bs fun x hx => hn x (List.mem_cons_of_mem _ hx)
    cases b
    · simpa using ih
    · simpa using hgh.mul hnf ih

namespace BData

variable (B : BData S T₁)

theorem ι_mem_normalizer_R1 (x : MB) : B.ι x ∈ normalizer (B.R1 : Set X) :=
  (actsR1_ι x).mem_normalizer fun g hg => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact MB.R1h_normal x a (MB.gensR1_mem a ha)

theorem S₁_le_normalizer_R1 : B.G.D₁.S₁ ≤ normalizer (B.R1 : Set X) := by
  intro g hg
  obtain ⟨x, rfl⟩ := B.exists_ι hg
  exact B.ι_mem_normalizer_R1 x

variable {B}

theorem ActsR1.actsAs_of_eq {g g' : X} {f : List MB} (hg : B.ActsR1 g f) (hg' : B.ActsR1 g' f) :
    ActsAs B.R1 g g' := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hg x hx, hg' x hx]

theorem g0_acts {D : MB.LiftData} (hD : D ∈ MB.liftList)
    (hd : B.ActsR1 C.d (MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2))
    (hdm : ∀ g ∈ MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2, MB.inR1 g = true) :
    B.ActsR1 ((B.ι MB.w₂ * C.d) * ((B.ι MB.w₂ * C.d) * (B.ι MB.w₂ * C.d))) D.chat := by
  have hψ : B.ActsR1 (B.ι MB.w₂ * C.d) (MB.psiOf D.o) := (actsR1_ι MB.w₂).mul hd hdm
  have hψm := MB.liftList_psi_mem D hD
  rw [MB.liftList_chat D hD]
  exact hψ.mul (hψ.mul hψ hψm) (MB.compR1_mem hψm)

variable (B)

structure R2Data where
  j : ℕ
  hj : j < 8
  c : X
  P : Subgroup X
  isPGroup : IsPGroup 2 P
  S₁_le : B.G.D₁.S₁ ≤ P
  c_mem : c ∈ P
  acts : B.ActsMB c (MB.r2Classes.getD j ([], 1)).1
  sq : c * c = B.ι (MB.r2Classes.getD j ([], 1)).2
  hd1 : C.d * C.d = 1 → j < 4
  hdt : C.d * C.d = t → 4 ≤ j

variable {B}

theorem exists_Z4_of_centralizer {P : Subgroup X} (hP : IsPGroup 2 P) {e : X} (heP : e ∈ P)
    (hec : e ∈ centralizer (B.R1 : Set X)) : ∃ e' ∈ MB.Z4, B.ι e' = e := by
  rcases B.eq_of_mem_centralizer_R1 hP heP hec with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [MB.Z4], map_one _⟩
  · exact ⟨MB.z, by simp [MB.Z4], B.ι_z⟩
  · exact ⟨MB.k, by simp [MB.Z4], B.ι_k⟩
  · exact ⟨MB.z * MB.k, by simp [MB.Z4], by rw [map_mul, B.ι_z, B.ι_k]⟩

theorem mem_centralizer_of_actsAs {g h : X} (hgh : ActsAs B.R1 g h) :
    h⁻¹ * g ∈ centralizer (B.R1 : Set X) := by
  rw [mem_centralizer_iff]
  intro r hr
  have := hgh r hr
  calc r * (h⁻¹ * g) = h⁻¹ * (h * r * h⁻¹) * g := by group
    _ = h⁻¹ * (g * r * g⁻¹) * g := by rw [this]
    _ = h⁻¹ * g * r := by group

theorem chat_mem {D : MB.LiftData} (hD : D ∈ MB.liftList) : ∀ x ∈ D.chat, MB.inR1 x = true := by
  rw [MB.liftList_chat D hD]
  exact MB.compR1_mem (MB.liftList_psi_mem D hD)

theorem exists_c {D : MB.LiftData} (hD : D ∈ MB.liftList)
    (hd : B.ActsR1 C.d (MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2))
    (hdm : ∀ g ∈ MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2, MB.inR1 g = true) :
    ∃ P : Subgroup X, IsPGroup 2 P ∧ B.G.D₁.S₁ ≤ P ∧ ∃ c ∈ P,
      ActsAs B.R1 c ((B.ι MB.w₂ * C.d) * ((B.ι MB.w₂ * C.d) * (B.ι MB.w₂ * C.d))) := by
  set g₀ := (B.ι MB.w₂ * C.d) * ((B.ι MB.w₂ * C.d) * (B.ι MB.w₂ * C.d)) with hg₀
  have hact := g0_acts hD hd hdm
  have hcm := chat_mem hD
  have hg₀N : g₀ ∈ normalizer (B.R1 : Set X) := hact.mem_normalizer hcm
  obtain ⟨hlen, hsp⟩ := MB.liftList_sp D hD
  have hgen : ∀ i : Fin 8, ActsAs B.R1 (g₀ * B.ι (MB.gens.getD i 1) * g₀⁻¹)
      (B.ι (D.sp.getD i 1)) := by
    intro i
    refine actsAs_conj_of hg₀N ?_
    have h1 := hact.mul (actsR1_ι (MB.gens.getD i 1)) (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact MB.R1h_normal _ a (MB.gensR1_mem a ha))
    have h2 := (actsR1_ι (D.sp.getD i 1)).mul hact hcm
    rw [hsp i] at h1
    exact h1.actsAs_of_eq h2
  have h2 : ∀ h ∈ B.G.D₁.S₁, ∃ h' ∈ B.G.D₁.S₁, ActsAs B.R1 (g₀ * h * g₀⁻¹) h' := by
    intro h hh
    obtain ⟨x, rfl⟩ := B.exists_ι hh
    refine ⟨B.ι (Sec8.nfProd D.sp (MB.nfBits x)), B.ι_mem_S₁ _, ?_⟩
    have e1 : g₀ * B.ι x * g₀⁻¹ = Sec8.nfProd (MB.gens.map fun a => g₀ * B.ι a * g₀⁻¹)
        (MB.nfBits x) := by
      conv_lhs => rw [MB.nf_spec x]
      exact map_nfProd ((MulAut.conj g₀).toMonoidHom.comp B.ι) _ _
    rw [e1, map_nfProd]
    refine ActsAs.nfProd _ _ _ ?_ fun h hh => ?_
    · have hf : ∀ i : Fin 8, ActsAs B.R1 ((MB.gens.map fun a => g₀ * B.ι a * g₀⁻¹).getD i 1)
          ((D.sp.map B.ι).getD i 1) := by
        intro i
        have := hgen i
        rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
          List.getElem?_map, show MB.gens[(i : ℕ)]? = some (MB.gens.getD i 1) by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [MB.gens])]; rfl,
          show D.sp[(i : ℕ)]? = some (D.sp.getD i 1) by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlen])]; rfl]
      generalize hL : D.sp = L at hf hlen
      match L, hlen with
      | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
        simp only [MB.gens, List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil,
          and_true]
        exact ⟨hf 0, hf 1, hf 2, hf 3, hf 4, hf 5, hf 6, hf 7⟩
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hh
      exact B.ι_mem_normalizer_R1 a
  have h3 : ∃ h₀ ∈ B.G.D₁.S₁, ActsAs B.R1 (g₀ * g₀) h₀ := by
    refine ⟨B.ι D.s0, B.ι_mem_S₁ _, ?_⟩
    have h1 := hact.mul hact hcm
    rw [MB.liftList_s0 D hD] at h1
    exact h1.actsAs_of_eq (actsR1_ι D.s0)
  have h4 : ∀ h ∈ B.G.D₁.S₁, ¬ ActsAs B.R1 g₀ h := by
    intro h hh hgh
    obtain ⟨x, rfl⟩ := B.exists_ι hh
    have := hact.eq_of_actsAs (actsR1_ι x) hgh MB.k (by decide +kernel)
    rw [MB.applyR1_k _ (MB.liftList_len D hD), MB.liftList_k D hD,
      MB.applyR1_k _ (by simp [MB.conjR1, MB.gensR1]),
      show (MB.conjR1 x).getD 6 1 = x * MB.k * x⁻¹ by simp [MB.conjR1, MB.gensR1],
      ← (MB.center_mem x).2, mul_inv_cancel_right] at this
    exact absurd (mul_eq_right.mp this) (by decide +kernel)
  obtain ⟨P, hP, hSP, -, hc⟩ := exists_actsAs B.isPGroup_S₁ B.S₁_le_normalizer_R1 hg₀N h2 h3 h4
  exact ⟨P, hP, hSP, hc⟩

theorem actsMB_eq {g : X} {f f' : List MB} (h : B.ActsMB g f) (h' : B.ActsMB g f')
    (hf : f.length = 8) (hf' : f'.length = 8) : f = f' := by
  rw [← MB.applyMB_gens f hf, ← MB.applyMB_gens f' hf']
  refine List.map_congr_left fun x _ => B.ι_injective ?_
  rw [← h x, ← h' x]

theorem sigOf_length {D : MB.LiftData} (hD : D ∈ MB.liftList) (e1 : MB) :
    (MB.sigOf D e1).length = 8 := by
  simp [MB.sigOf, MB.liftList_len D hD]

theorem r2Data_of {D : MB.LiftData} (hD : D ∈ MB.liftList)
    (hd : B.ActsR1 C.d (MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2))
    (hdm : ∀ g ∈ MB.dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2, MB.inR1 g = true) :
    ∃ q ∈ D.norms, ∃ P : Subgroup X, IsPGroup 2 P ∧ B.G.D₁.S₁ ≤ P ∧ ∃ c ∈ P,
      B.ActsMB c (MB.r2Classes.getD q.2.2.1 ([], 1)).1 ∧
      c * c = B.ι (MB.r2Classes.getD q.2.2.1 ([], 1)).2 := by
  obtain ⟨P, hP, hSP, c, hcP, hc⟩ := exists_c hD hd hdm
  set g₀ := (B.ι MB.w₂ * C.d) * ((B.ι MB.w₂ * C.d) * (B.ι MB.w₂ * C.d)) with hg₀
  have hact := g0_acts hD hd hdm
  have hcm := chat_mem hD
  have hg₀N : g₀ ∈ normalizer (B.R1 : Set X) := hact.mem_normalizer hcm
  have hcR : B.ActsR1 c D.chat := by
    intro x hx
    rw [← hact x hx]
    exact hc _ ⟨x, hx, rfl⟩
  have hcN : c ∈ normalizer (B.R1 : Set X) := hcR.mem_normalizer hcm
  obtain ⟨hlen, hsp⟩ := MB.liftList_sp D hD
  have hw : ActsAs B.R1 (c * B.ι MB.w₂ * c⁻¹) (B.ι (D.sp.getD 0 1)) := by
    refine (ActsAs.conj hc hcN (B.ι_mem_normalizer_R1 _)).trans ?_
    refine actsAs_conj_of hg₀N ?_
    have h1 := hact.mul (actsR1_ι MB.w₂) (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact MB.R1h_normal _ a (MB.gensR1_mem a ha))
    have h2 := (actsR1_ι (D.sp.getD 0 1)).mul hact hcm
    rw [show MB.w₂ = MB.gens.getD (0 : Fin 8) 1 from rfl, hsp 0] at h1
    exact h1.actsAs_of_eq h2
  obtain ⟨e1, he1, hwe⟩ := exists_Z4_of_centralizer hP (mul_mem (inv_mem (hSP (B.ι_mem_S₁ _)))
    (mul_mem (mul_mem hcP (hSP (B.ι_mem_S₁ _))) (inv_mem hcP))) (mem_centralizer_of_actsAs hw)
  have hsq : ActsAs B.R1 (c * c) (B.ι D.s0) := by
    have h1 := hcR.mul hcR hcm
    rw [MB.liftList_s0 D hD] at h1
    exact h1.actsAs_of_eq (actsR1_ι D.s0)
  obtain ⟨e2, he2, hse⟩ := exists_Z4_of_centralizer hP (mul_mem (inv_mem (hSP (B.ι_mem_S₁ _)))
    (mul_mem hcP hcP)) (mem_centralizer_of_actsAs hsq)
  have hc2 : c * c = B.ι (D.s0 * e2) := by rw [map_mul, hse]; group
  have hσ : B.ActsMB c (MB.sigOf D e1) := by
    refine actsMB_of_map ?_
    have hw' : c * B.ι MB.w₂ * c⁻¹ = B.ι (D.sp.getD 0 1 * e1) := by rw [map_mul, hwe]; group
    have hgens := MB.liftList_chat_gens D hD
    have hR : ∀ g ∈ MB.gensR1, c * B.ι g * c⁻¹ = B.ι (MB.applyR1 D.chat g) :=
      fun g hg => hcR g (MB.gensR1_mem g hg)
    rw [MB.sigOf, show MB.gens = MB.w₂ :: MB.gensR1 from rfl, List.map_cons, List.map_cons,
      hw', ← hgens, List.map_map]
    congr 1
    · congr 2
      cases D.sp <;> rfl
    · exact List.map_congr_left fun g hg => hR g hg
  have hlenσ := sigOf_length hD e1
  have h2' : MB.applyMB (MB.sigOf D e1) (D.s0 * e2) = D.s0 * e2 := by
    apply B.ι_injective
    rw [← hσ, ← hc2]
    group
  have h3' : MB.compMB (MB.sigOf D e1) (MB.sigOf D e1) = MB.conjMB (D.s0 * e2) := by
    refine actsMB_eq (hσ.mul hσ) ?_ (by simp [MB.compMB, hlenσ]) (by simp [MB.conjMB, MB.gens])
    rw [hc2]; exact actsMB_ι _
  obtain ⟨q, hq, hq1, hq2⟩ := MB.liftList_combos D hD e1 he1 e2 he2 h2' h3'
  obtain ⟨-, hn1, hn2⟩ := MB.liftList_norms D hD q hq
  refine ⟨q, hq, P, hP, hSP, c * B.ι q.2.2.2, mul_mem hcP (hSP (B.ι_mem_S₁ _)), ?_, ?_⟩
  · rw [← hn1, hq1]
    exact hσ.mul (actsMB_ι _)
  · rw [← hn2, hq1, hq2]
    calc c * B.ι q.2.2.2 * (c * B.ι q.2.2.2) =
        (c * B.ι q.2.2.2 * c⁻¹) * (c * c) * B.ι q.2.2.2 := by group
      _ = _ := by rw [hσ, hc2, ← map_mul, ← map_mul]

variable (B) in
theorem nonempty_r2Data : Nonempty (R2Data B) := by
  have ht1 : t ≠ 1 := fun h => by
    have := A.orderOf_t
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  rcases KD8ab.d_sq (C := C) with hsq | hsq
  · have hd1 : C.d * C.d = 1 := by rw [← pow_two]; exact hsq
    obtain ⟨o, ho, hd⟩ := B.exists_dValid1 hd1
    rw [← MB.liftList_o1] at ho
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp ho
    have hD' : D ∈ MB.liftList := List.mem_of_mem_take hD
    obtain ⟨q, hq, P, hP, hSP, c, hcP, hσ, hc2⟩ := r2Data_of hD' hd
      (MB.liftList_dImgs_mem D hD')
    exact ⟨⟨q.2.2.1, MB.liftList_norms_lt D hD' q hq, c, P, hP, hSP, hcP, hσ, hc2,
      fun _ => MB.liftList_d1 D hD q hq, fun h => absurd (hd1.symm.trans h).symm ht1⟩⟩
  · have hdt : C.d * C.d = t := by rw [← pow_two]; exact hsq
    obtain ⟨o, ho, hd⟩ := B.exists_dValidT hdt
    rw [← MB.liftList_oT] at ho
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp ho
    have hD' : D ∈ MB.liftList := List.mem_of_mem_drop hD
    obtain ⟨q, hq, P, hP, hSP, c, hcP, hσ, hc2⟩ := r2Data_of hD' hd
      (MB.liftList_dImgs_mem D hD')
    exact ⟨⟨q.2.2.1, MB.liftList_norms_lt D hD' q hq, c, P, hP, hSP, hcP, hσ, hc2,
      fun h => absurd (hdt.symm.trans h) ht1, fun _ => MB.liftList_dT D hD q hq⟩⟩

end BData

end KD8abB

end CFSG.OddStandard.SmallF3.L33.KD
