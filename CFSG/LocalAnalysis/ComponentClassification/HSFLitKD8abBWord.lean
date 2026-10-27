module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBDelta
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBR2

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def letterAct (fd cQ : List MB) : ℕ → List MB
  | 0 => fd
  | 1 => compQ1 fd fd
  | 2 => cQ
  | 3 => conjQ1 w₂
  | 4 => conjQ1 u
  | 5 => conjQ1 w₁
  | 6 => conjQ1 v
  | _ => conjQ1 t

@[expose] def wordAct (fd cQ : List MB) (w : List ℕ) : List MB :=
  w.foldr (fun l acc => compQ1 (letterAct fd cQ l) acc) gensQ1

@[expose] def restrQ1 (σ : List MB) : List MB := gensQ1.map (applyMB σ)

@[expose] def KillOK (fw sp : List MB) (s0 : MB) : Prop :=
  sp.length = 8 ∧ (∀ i : Fin 8, compQ1 fw (conjQ1 (gens.getD i 1)) =
    compQ1 (conjQ1 (sp.getD i 1)) fw) ∧ compQ1 fw fw = conjQ1 s0 ∧
    (∀ s : MB, fw ≠ conjQ1 s) ∧ inE0 (fw.getD 3 1) = true ∧ inE0 (fw.getD 4 1) = true ∧
    inE0 (fw.getD 6 1) = true ∧ inE0 (fw.getD 5 1 * t) = true ∧ fw.length = 7

instance (fw sp : List MB) (s0 : MB) : Decidable (KillOK fw sp s0) := by
  unfold KillOK; infer_instance

theorem inE1_of_inE0_mul_t : ∀ x : MB, inE0 (x * t) = true → inE1 x = true := by decide +kernel

theorem inE1_of_inE0 : ∀ x : MB, inE0 x = true → inE1 x = true := by decide +kernel

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable (B : BData S T₁)

@[expose] def letterElt (δ c : X) : ℕ → X
  | 0 => δ
  | 1 => δ⁻¹
  | 2 => c
  | 3 => B.ι MB.w₂
  | 4 => B.ι MB.u
  | 5 => B.ι MB.w₁
  | 6 => B.ι MB.v
  | _ => B.ι MB.t

@[expose] def wordElt (δ c : X) (w : List ℕ) : X := (w.map (B.letterElt δ c)).prod

variable {B}

theorem conjQ1_mem (s : MB) : ∀ x ∈ MB.conjQ1 s, MB.inQ1 x = true := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact MB.Q1h_normal s a (MB.gensQ1_mem a ha)

theorem ActsMB.actsQ1 {g : X} {σ : List MB} (h : B.ActsMB g σ) :
    B.ActsQ1 g (MB.restrQ1 σ) := by
  refine actsQ1_of_map ?_
  rw [MB.restrQ1, List.map_map]
  exact List.map_congr_left fun a _ => h a

theorem actsQ1_inv {δ : X} {f : List MB} (hδ : B.ActsQ1 δ f) (hf : ∀ x ∈ f, MB.inQ1 x = true)
    (h3 : MB.compQ1 f (MB.compQ1 f f) = MB.gensQ1) : B.ActsQ1 δ⁻¹ (MB.compQ1 f f) := by
  have h2 := hδ.mul hδ hf
  have h3' := hδ.mul h2 (MB.compQ1_mem hf)
  rw [h3] at h3'
  intro x hx
  have e1 := h3' x hx
  rw [MB.applyQ1, ← MB.nf_Q1 hx] at e1
  calc δ⁻¹ * B.ι x * δ⁻¹⁻¹ = δ⁻¹ * (δ * (δ * δ) * B.ι x * (δ * (δ * δ))⁻¹) * δ := by
        rw [e1]; group
    _ = δ * δ * B.ι x * (δ * δ)⁻¹ := by group
    _ = _ := h2 x hx

theorem letterAct_mem {fd cQ : List MB} (hfd : ∀ x ∈ fd, MB.inQ1 x = true)
    (hcQ : ∀ x ∈ cQ, MB.inQ1 x = true) : ∀ l, ∀ x ∈ MB.letterAct fd cQ l, MB.inQ1 x = true
  | 0 => hfd
  | 1 => MB.compQ1_mem hfd
  | 2 => hcQ
  | 3 => conjQ1_mem _
  | 4 => conjQ1_mem _
  | 5 => conjQ1_mem _
  | 6 => conjQ1_mem _
  | _ + 7 => conjQ1_mem _

theorem actsQ1_letter {δ c : X} {fd cQ : List MB} (hδ : B.ActsQ1 δ fd)
    (hfd : ∀ x ∈ fd, MB.inQ1 x = true) (h3 : MB.compQ1 fd (MB.compQ1 fd fd) = MB.gensQ1)
    (hc : B.ActsQ1 c cQ) : ∀ l, B.ActsQ1 (B.letterElt δ c l) (MB.letterAct fd cQ l)
  | 0 => hδ
  | 1 => actsQ1_inv hδ hfd h3
  | 2 => hc
  | 3 => actsQ1_ι _
  | 4 => actsQ1_ι _
  | 5 => actsQ1_ι _
  | 6 => actsQ1_ι _
  | _ + 7 => actsQ1_ι _

theorem actsQ1_one : B.ActsQ1 1 MB.gensQ1 := fun x hx => by
  rw [one_mul, inv_one, mul_one, MB.applyQ1, ← MB.nf_Q1 hx]

theorem actsQ1_wordElt {δ c : X} {fd cQ : List MB} (hδ : B.ActsQ1 δ fd)
    (hfd : ∀ x ∈ fd, MB.inQ1 x = true) (h3 : MB.compQ1 fd (MB.compQ1 fd fd) = MB.gensQ1)
    (hc : B.ActsQ1 c cQ) (hcQ : ∀ x ∈ cQ, MB.inQ1 x = true) :
    ∀ w : List ℕ, B.ActsQ1 (B.wordElt δ c w) (MB.wordAct fd cQ w)
  | [] => by simpa [wordElt, MB.wordAct] using actsQ1_one
  | l :: w => by
    have ih := actsQ1_wordElt hδ hfd h3 hc hcQ w
    have hl := actsQ1_letter hδ hfd h3 hc l
    have hm : ∀ x ∈ MB.wordAct fd cQ w, MB.inQ1 x = true := by
      cases w with
      | nil => exact fun x hx => MB.gensQ1_mem x hx
      | cons l' w' => exact MB.compQ1_mem (letterAct_mem hfd hcQ l')
    simpa [wordElt, MB.wordAct] using hl.mul ih hm

theorem ι_mem_normalizer_Q1 (x : MB) : B.ι x ∈ normalizer (B.Q1 : Set X) :=
  (actsQ1_ι x).mem_normalizer (conjQ1_mem x)

theorem S₁_le_normalizer_Q1 : B.G.D₁.S₁ ≤ normalizer (B.Q1 : Set X) := by
  intro g hg
  obtain ⟨x, rfl⟩ := B.exists_ι hg
  exact ι_mem_normalizer_Q1 x

theorem ActsQ1.actsAs_of_eq {g g' : X} {f : List MB} (hg : B.ActsQ1 g f) (hg' : B.ActsQ1 g' f) :
    ActsAs B.Q1 g g' := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hg x hx, hg' x hx]

theorem ActsQ1.eq_conj {g : X} {f : List MB} {s : MB} (hg : B.ActsQ1 g f) (hf : f.length = 7)
    (h : ActsAs B.Q1 g (B.ι s)) : f = MB.conjQ1 s := by
  have hmap : MB.gensQ1.map (MB.applyQ1 f) = MB.gensQ1.map (MB.applyQ1 (MB.conjQ1 s)) :=
    List.map_congr_left fun x hx =>
      hg.eq_of_actsAs (actsQ1_ι s) h x (MB.gensQ1_mem x hx)
  calc f = MB.gensQ1.map (MB.applyQ1 f) := (MB.applyQ1_gens f hf).symm
    _ = MB.gensQ1.map (MB.applyQ1 (MB.conjQ1 s)) := hmap
    _ = MB.conjQ1 s := MB.applyQ1_gens _ (by simp [MB.conjQ1, MB.gensQ1_length])

theorem false_of_kill {g₀ : X} {fw sp : List MB} {s0 : MB} (hg : B.ActsQ1 g₀ fw)
    (hfw : ∀ x ∈ fw, MB.inQ1 x = true) (hK : MB.KillOK fw sp s0) : False := by
  obtain ⟨hlen, hsp, hs0, hnot, hz, hy, hk, ht, hflen⟩ := hK
  have hg₀N : g₀ ∈ normalizer (B.Q1 : Set X) := hg.mem_normalizer hfw
  have hgen : ∀ i : Fin 8, ActsAs B.Q1 (g₀ * B.ι (MB.gens.getD i 1) * g₀⁻¹)
      (B.ι (sp.getD i 1)) := by
    intro i
    refine actsAs_conj_of hg₀N ?_
    have h1 := hg.mul (actsQ1_ι (MB.gens.getD i 1)) (conjQ1_mem _)
    have h2 := (actsQ1_ι (sp.getD i 1)).mul hg hfw
    rw [hsp i] at h1
    exact h1.actsAs_of_eq h2
  have h2 : ∀ h ∈ B.G.D₁.S₁, ∃ h' ∈ B.G.D₁.S₁, ActsAs B.Q1 (g₀ * h * g₀⁻¹) h' := by
    intro h hh
    obtain ⟨x, rfl⟩ := B.exists_ι hh
    refine ⟨B.ι (Sec8.nfProd sp (MB.nfBits x)), B.ι_mem_S₁ _, ?_⟩
    have e1 : g₀ * B.ι x * g₀⁻¹ = Sec8.nfProd (MB.gens.map fun a => g₀ * B.ι a * g₀⁻¹)
        (MB.nfBits x) := by
      conv_lhs => rw [MB.nf_spec x]
      exact map_nfProd ((MulAut.conj g₀).toMonoidHom.comp B.ι) _ _
    rw [e1, map_nfProd]
    refine ActsAs.nfProd _ _ _ ?_ fun h hh => ?_
    · have hf : ∀ i : Fin 8, ActsAs B.Q1 ((MB.gens.map fun a => g₀ * B.ι a * g₀⁻¹).getD i 1)
          ((sp.map B.ι).getD i 1) := by
        intro i
        have := hgen i
        rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
          List.getElem?_map, show MB.gens[(i : ℕ)]? = some (MB.gens.getD i 1) by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [MB.gens])]; rfl,
          show sp[(i : ℕ)]? = some (sp.getD i 1) by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hlen])]; rfl]
      generalize hL : sp = L' at hf hlen
      match L', hlen with
      | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
        simp only [MB.gens, List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil,
          and_true]
        exact ⟨hf 0, hf 1, hf 2, hf 3, hf 4, hf 5, hf 6, hf 7⟩
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hh
      exact ι_mem_normalizer_Q1 a
  have h3 : ∃ h₀ ∈ B.G.D₁.S₁, ActsAs B.Q1 (g₀ * g₀) h₀ := by
    refine ⟨B.ι s0, B.ι_mem_S₁ _, ?_⟩
    have h1 := hg.mul hg hfw
    rw [hs0] at h1
    exact h1.actsAs_of_eq (actsQ1_ι s0)
  have h4 : ∀ h ∈ B.G.D₁.S₁, ¬ ActsAs B.Q1 g₀ h := by
    intro h hh hgh
    obtain ⟨x, rfl⟩ := B.exists_ι hh
    exact hnot x (hg.eq_conj hflen hgh)
  obtain ⟨P, hP, hSP, -, c', hc'P, hc'⟩ :=
    exists_actsAs B.isPGroup_S₁ S₁_le_normalizer_Q1 hg₀N h2 h3 h4
  have hc'f : B.ActsQ1 c' fw := by
    intro x hx
    rw [← hg x hx]
    exact hc' _ ⟨x, hx, rfl⟩
  have hE : c' ∈ normalizer (S.E S.y : Set X) := by
    refine mem_normalizer_of_conj_le fun e he => ?_
    obtain ⟨x, hx, rfl⟩ := B.mem_E₁_iff.mp he
    obtain ⟨bs, -, rfl⟩ := MB.E1h_span x hx
    have e1 : c' * B.ι (Sec8.nfProd [MB.z, MB.y, MB.t, MB.k] bs) * c'⁻¹ =
        Sec8.nfProd ([MB.z, MB.y, MB.t, MB.k].map fun a => c' * B.ι a * c'⁻¹) bs :=
      map_nfProd ((MulAut.conj c').toMonoidHom.comp B.ι) _ _
    rw [e1]
    refine nfProd_mem _ _ fun g hg => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
    have hq : ∀ a : MB, MB.inQ1 a = true → MB.inE1 (MB.applyQ1 fw a) = true →
        c' * B.ι a * c'⁻¹ ∈ S.E S.y := fun a ha h => by
      rw [hc'f a ha]; exact B.ι_mem_E₁ h
    have hgens := MB.applyQ1_gens fw hflen
    have e2 : ∀ i : Fin 7, MB.applyQ1 fw (MB.gensQ1.getD i 1) = fw.getD i 1 := by
      intro i
      have := congrArg (fun L => L.getD i 1) hgens
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
      rw [List.getElem?_eq_getElem (by simp [MB.gensQ1_length])] at this ⊢
      exact this
    have ez : MB.applyQ1 fw MB.z = fw.getD 3 1 := e2 3
    have ey : MB.applyQ1 fw MB.y = fw.getD 4 1 := e2 4
    have et : MB.applyQ1 fw MB.t = fw.getD 5 1 := e2 5
    have ek : MB.applyQ1 fw MB.k = fw.getD 6 1 := e2 6
    rcases hg with rfl | rfl | rfl | rfl
    · exact hq MB.z (by decide +kernel) (by rw [ez]; exact MB.inE1_of_inE0 _ hz)
    · exact hq MB.y (by decide +kernel) (by rw [ey]; exact MB.inE1_of_inE0 _ hy)
    · exact hq MB.t (by decide +kernel) (by rw [et]; exact MB.inE1_of_inE0_mul_t _ ht)
    · exact hq MB.k (by decide +kernel) (by rw [ek]; exact MB.inE1_of_inE0 _ hk)
  have hmax := B.G.D₁.S₁_maximal (B.G.D₁.S₁ ⊔ zpowers c')
    (hP.to_le (sup_le hSP (zpowers_le.mpr hc'P))) le_sup_left
    (sup_le B.G.D₁.S₁_le (zpowers_le.mpr hE))
  have hc'S : c' ∈ B.G.D₁.S₁ := hmax ▸ mem_sup_right (mem_zpowers c')
  obtain ⟨x, rfl⟩ := B.exists_ι hc'S
  exact h4 _ (B.ι_mem_S₁ x) fun r hr => (hc' r hr).symm

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
