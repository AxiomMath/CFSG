module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureFrame
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Balance (oddCoreIn)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {A H : Subgroup G} {S : Set (Subgroup G)}

section Closure

variable (p f) in
@[expose] def omegaStarIn (H : Subgroup G) (Ω : Set (Subgroup G)) (A : Subgroup G)
    (S : Set (Subgroup G)) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ H, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember p f K z ∧ IsClassicalMember p f L (h * z * h⁻¹)}

theorem le_of_mem_omegaStarIn (hΩ : InClass p f Ω)
    (hH : ∀ a ∈ A, IsFrameInvolution p f S a → centralizingLayer Ω {a} ≤ H) {L : Subgroup G}
    (hLs : L ∈ omegaStarIn p f H Ω A S) : L ≤ H := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hLa' := isClassicalMember_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hΩ.conjInvariant _ _ hLΩ, le_centralizer hLa'⟩
  have hY : conjSub h⁻¹ L ≤ H := (le_centralizingLayer hmem).trans (hH a haA ⟨K, hK, hKa⟩)
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarIn_of_commutes (hΩ : InClass p f Ω)
    (hH : ∀ a ∈ A, IsFrameInvolution p f S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarIn p f H Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarIn p f H Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hlink a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hz₀' : IsClassicalMember p f M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember p f L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hH a haA ⟨K, hKS, hKa⟩ hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem mem_omegaStarIn_of_omegaConnected (hΩ : InClass p f Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hH : ∀ a ∈ A, IsFrameInvolution p f S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) :
    L ∈ omegaStarIn p f H Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨z, hzA, hz⟩ := hinv K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarIn p f H Ω A S :=
    ⟨hS hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarIn p f H Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarIn_of_commutes hΩ hH hlink ih hbc.1 hbc.2
  exact key L (hconn K₀ (hS hK₀) L hLΩ)

theorem eq_top_of_layer_le (hΩ : InClass p f Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hH : ∀ a ∈ A, IsFrameInvolution p f S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    (hconn : OmegaConnected Ω) : H = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_of_mem_omegaStarIn hΩ hH
    (mem_omegaStarIn_of_omegaConnected hΩ hS hne hinv hH hlink hconn hLΩ)

end Closure

section Layers

variable (p f) in
@[expose] def frameLayerSpan (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Subgroup G :=
  ⨆ a ∈ A, ⨆ (_ : IsFrameInvolution p f S a), centralizingLayer Ω {a}

theorem centralizingLayer_le_frameLayerSpan {a : G} (ha : a ∈ A) (hfa : IsFrameInvolution p f S a) :
    centralizingLayer Ω {a} ≤ frameLayerSpan p f Ω A S :=
  le_iSup₂_of_le a ha (le_iSup (fun _ : IsFrameInvolution p f S a => centralizingLayer Ω {a}) hfa)

theorem frameLayerSpan_eq_top (hΩ : InClass p f Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    (hconn : OmegaConnected Ω) : frameLayerSpan p f Ω A S = ⊤ :=
  eq_top_of_layer_le hΩ hS hne hinv (fun _ ha hfa => centralizingLayer_le_frameLayerSpan ha hfa)
    hlink hconn

theorem frameCentralizerSpan_eq_top (hΩ : InClass p f Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    (hconn : OmegaConnected Ω) :
    (⨆ a ∈ A, ⨆ (_ : IsFrameInvolution p f S a), Subgroup.centralizer ({a} : Set G)) = ⊤ :=
  top_unique ((frameLayerSpan_eq_top hΩ hS hne hinv hlink hconn).symm.le.trans
    (iSup₂_le fun a ha => iSup_le fun hfa => (centralizingLayer_le_centralizer Ω {a}).trans
      (le_iSup₂_of_le a ha (le_iSup (fun _ : IsFrameInvolution p f S a =>
        Subgroup.centralizer ({a} : Set G)) hfa))))

end Layers

section FrameSpan

variable (S) in
@[expose] def frameSpan (S : Set (Subgroup G)) : Subgroup G :=
  ⨆ K ∈ S, K

theorem le_frameSpan {K : Subgroup G} (hK : K ∈ S) : K ≤ frameSpan S :=
  le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ S) => K) K hK

theorem commutator_mul_central_left {Y : Subgroup G} {n a b : G}
    (hn : ∀ g ∈ Y, n * g = g * n) (ha : a ∈ Y) (hb : b ∈ Y) :
    n * a * b * (n * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hg : n * (a * b * a⁻¹) = a * b * a⁻¹ * n := hn _ (mul_mem (mul_mem ha hb) (inv_mem ha))
  calc n * a * b * (n * a)⁻¹ * b⁻¹ = n * (a * b * a⁻¹) * n⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * n * n⁻¹ * b⁻¹ := by rw [hg]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_mul_central_right {Y : Subgroup G} {n a b : G}
    (hn : ∀ g ∈ Y, n * g = g * n) (ha : a ∈ Y) (hb : b ∈ Y) :
    a * (n * b) * a⁻¹ * (n * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have ha' : a * n = n * a := (hn a ha).symm
  have hg : n * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * n :=
    hn _ (mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
  calc a * (n * b) * a⁻¹ * (n * b)⁻¹ = (a * n) * b * a⁻¹ * b⁻¹ * n⁻¹ := by group
    _ = n * (a * b * a⁻¹ * b⁻¹) * n⁻¹ := by rw [ha']; group
    _ = a * b * a⁻¹ * b⁻¹ * n * n⁻¹ := by rw [hg]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem exists_mul_of_mem_sup_of_central {N W Y : Subgroup G}
    (hN : ∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) (hWY : W ≤ Y) {x : G} (hx : x ∈ N ⊔ W) :
    ∃ n ∈ N, ∃ w ∈ W, x = n * w := by
  let C : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ w ∈ W, x = n * w}
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, w₁, hw₁, rfl⟩ ⟨n₂, hn₂, w₂, hw₂, rfl⟩
        refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, w₁ * w₂, mul_mem hw₁ hw₂, ?_⟩
        have h := hN n₂ hn₂ w₁ (hWY hw₁)
        calc n₁ * w₁ * (n₂ * w₂) = n₁ * (w₁ * n₂) * w₂ := by group
          _ = n₁ * (n₂ * w₁) * w₂ := by rw [h]
          _ = n₁ * n₂ * (w₁ * w₂) := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, hn, w, hw, rfl⟩
        refine ⟨n⁻¹, inv_mem hn, w⁻¹, inv_mem hw, ?_⟩
        have h := hN n⁻¹ (inv_mem hn) w⁻¹ (hWY (inv_mem hw))
        calc (n * w)⁻¹ = w⁻¹ * n⁻¹ := by group
          _ = n⁻¹ * w⁻¹ := h.symm }
  exact (sup_le (fun n hn => ⟨n, hn, 1, one_mem _, by simp⟩)
    (fun w hw => ⟨1, one_mem _, w, hw, by simp⟩) : N ⊔ W ≤ C) hx

theorem mul_comm_of_mem_oddCoreIn_of_localOddCentral {a : G} (h : LocalOddCentral Ω {a}) {n y : G}
    (hn : n ∈ oddCoreIn (centralizingLayer Ω {a})) (hy : y ∈ centralizingLayer Ω {a}) :
    n * y = y * n := by
  obtain ⟨n', hn', rfl⟩ := hn
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (h hn') ⟨y, hy⟩).symm

theorem centralizingLayer_le_of_localOddCentral (hΩ : InClass p f Ω) (hS : S ⊆ Ω) {a : G}
    (hP1 : LocalOddCentral Ω {a}) (hgen : FrameGenerationModO Ω S a) :
    centralizingLayer Ω {a} ≤
      ⨆ K ∈ S, ⨆ (_ : K ≤ Subgroup.centralizer ({a} : Set G)), K := by
  set Y := centralizingLayer Ω {a} with hY
  set W := ⨆ K ∈ S, ⨆ (_ : K ≤ Subgroup.centralizer ({a} : Set G)), K with hW
  have hWY : W ≤ Y :=
    iSup₂_le fun K hK => iSup_le fun hKa => le_centralizingLayer ⟨hS hK, hKa⟩
  have hdec : ∀ y ∈ Y, ∃ n ∈ oddCoreIn Y, ∃ w ∈ W, y = n * w := fun y hy =>
    exists_mul_of_mem_sup_of_central (fun n hn g hg => mul_comm_of_mem_oddCoreIn_of_localOddCentral
      hP1 hn hg) hWY (hgen hy)
  refine iSup₂_le fun L hL => ?_
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY : L ≤ Y := le_centralizingLayer hL
  have hcomm : commutator ↥L ≤ W.subgroupOf L := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨n₁, hn₁, w₁, hw₁, hx⟩ := hdec x (hLY x.2)
    obtain ⟨n₂, hn₂, w₂, hw₂, hy⟩ := hdec y (hLY y.2)
    have hc₁ : ∀ g ∈ Y, n₁ * g = g * n₁ := fun g hg =>
      mul_comm_of_mem_oddCoreIn_of_localOddCentral hP1 hn₁ hg
    have hc₂ : ∀ g ∈ Y, n₂ * g = g * n₂ := fun g hg =>
      mul_comm_of_mem_oddCoreIn_of_localOddCentral hP1 hn₂ hg
    have hyY : (y : G) ∈ Y := hLY y.2
    have hw₁Y := hWY hw₁
    have hw₂Y := hWY hw₂
    have hyY' : n₂ * w₂ ∈ Y := hy ▸ hyY
    have step : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ = w₁ * w₂ * w₁⁻¹ * w₂⁻¹ := by
      rw [hx, hy, commutator_mul_central_left hc₁ hw₁Y hyY',
        commutator_mul_central_right hc₂ hw₁Y hw₂Y]
    change (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ W
    rw [step]
    exact mul_mem (mul_mem (mul_mem hw₁ hw₂) (inv_mem hw₁)) (inv_mem hw₂)
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥L) ∈ commutator ↥L := by
    rw [hz.perfect.commutator_eq_top]
    exact Subgroup.mem_top _
  exact hcomm hxc

omit [Fact p.Prime] in
theorem iSup_centralizing_le_frameSpan (a : G) :
    (⨆ K ∈ S, ⨆ (_ : K ≤ Subgroup.centralizer ({a} : Set G)), K) ≤ frameSpan S :=
  iSup₂_le fun _ hK => iSup_le fun _ => le_frameSpan hK

theorem centralizingLayer_le_frameSpan_of_localOddCentral (hΩ : InClass p f Ω) (hS : S ⊆ Ω)
    {a : G} (hP1 : LocalOddCentral Ω {a}) (hgen : FrameGenerationModO Ω S a) :
    centralizingLayer Ω {a} ≤ frameSpan S :=
  (centralizingLayer_le_of_localOddCentral hΩ hS hP1 hgen).trans (iSup_centralizing_le_frameSpan a)

omit [Fact p.Prime] in
theorem centralizingLayer_le_frameSpan_of_oddCoreIn_le {a : G}
    (hodd : oddCoreIn (centralizingLayer Ω {a}) ≤ frameSpan S)
    (hgen : FrameGenerationModO Ω S a) : centralizingLayer Ω {a} ≤ frameSpan S :=
  hgen.trans (sup_le hodd (iSup_centralizing_le_frameSpan a))

theorem frameSpan_eq_top (hΩ : InClass p f Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hlayer : ∀ a ∈ A, IsFrameInvolution p f S a → centralizingLayer Ω {a} ≤ frameSpan S)
    (hlink : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a)
    (hconn : OmegaConnected Ω) : frameSpan S = ⊤ :=
  eq_top_of_layer_le hΩ hS hne hinv hlayer hlink hconn

theorem frameSpan_eq_top_of_lie [Finite G] (hL : LocalHypotheses p f Ω A) (hS : S ⊆ Ω)
    (hne : S.Nonempty) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hgen : ∀ a ∈ A, IsFrameInvolution p f S a → FrameGenerationModO Ω S a)
    (hP1 : ∀ a ∈ A, IsFrameInvolution p f S a → LocalOddCentral Ω {a})
    (hconn : OmegaConnected Ω) : frameSpan S = ⊤ :=
  frameSpan_eq_top hL.inClass hS hne hinv
    (fun a ha hfa => centralizingLayer_le_frameSpan_of_localOddCentral hL.inClass hS
      (hP1 a ha hfa) (hgen a ha hfa))
    (fun a ha hfa => by
      obtain ⟨K, hKS, hK⟩ := hfa
      exact involutionLink_of_lie hL ha hK.ne_one hS hinv
        ((hgen a ha ⟨K, hKS, hK⟩).cover hL.inClass hS))
    hconn

end FrameSpan

section Lie

theorem frameLayerSpan_eq_top_of_lie [Finite G] (hL : LocalHypotheses p f Ω A) (hS : S ⊆ Ω)
    (hne : S.Nonempty) (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f S a → FrameCoversModO Ω S a)
    (hconn : OmegaConnected Ω) : frameLayerSpan p f Ω A S = ⊤ :=
  frameLayerSpan_eq_top hL.inClass hS hne hinv
    (fun a ha hfa => by
      obtain ⟨K, hKS, hK⟩ := hfa
      exact involutionLink_of_lie hL ha hK.ne_one hS hinv (hcover a ha ⟨K, hKS, hK⟩))
    hconn

end Lie

end CFSG.ClassicalInvolution.Generic.DeltaClosure
