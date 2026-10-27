module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBLift
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBCoord
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT2e

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def bitsR1 (x : MB) : List Bool :=
  [bit x 1, bit x 2, bit x 3, bit x 4, bit x 5, bit x 6, bit x 7]

@[expose] def bitsQ1 (x : MB) : List Bool :=
  [bit x 0, bit x 2, bit x 3, bit x 4, bit x 5, bit x 6, bit x 7]

@[expose] def applyR1 (f : List MB) (x : MB) : MB := nfProd f (bitsR1 x)

@[expose] def applyQ1 (f : List MB) (x : MB) : MB := nfProd f (bitsQ1 x)

@[expose] def applyMB (f : List MB) (x : MB) : MB := nfProd f (nfBits x)

@[expose] def compMB (f g : List MB) : List MB := g.map (applyMB f)

@[expose] def conjMB (s : MB) : List MB := gens.map fun g => s * g * s⁻¹

@[expose] def compR1 (f g : List MB) : List MB := g.map (applyR1 f)

@[expose] def compQ1 (f g : List MB) : List MB := g.map (applyQ1 f)

@[expose] def conjR1 (s : MB) : List MB := gensR1.map fun g => s * g * s⁻¹

@[expose] def conjQ1 (s : MB) : List MB := gensQ1.map fun g => s * g * s⁻¹

theorem nf_R1 {x : MB} (hx : inR1 x = true) : x = nfProd gensR1 (bitsR1 x) := by
  have h0 : bit x 0 = false := by simpa [inR1] using hx
  conv_lhs => rw [nf_bits x]
  simp only [h0, gensR1, bitsR1, nfProd, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]

theorem nf_Q1 {x : MB} (hx : inQ1 x = true) : x = nfProd gensQ1 (bitsQ1 x) := by
  have h1 : bit x 1 = false := by simpa [inQ1] using hx
  conv_lhs => rw [nf_bits x]
  simp only [h1, gensQ1, bitsQ1, nfProd, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem nfProd_mem {G : Type*} [Group G] {H : Subgroup G} :
    ∀ (L : List G) (bs : List Bool), (∀ g ∈ L, g ∈ H) → nfProd L bs ∈ H
  | [], _, _ => by simp [nfProd]
  | _ :: _, [], _ => by simp [nfProd]
  | g :: gs, b :: bs, h => by
    simp only [nfProd]
    refine mul_mem ?_ (nfProd_mem gs bs fun x hx => h x (List.mem_cons_of_mem _ hx))
    split_ifs
    · exact h g List.mem_cons_self
    · exact one_mem H

namespace BData

variable (B : BData S T₁)

@[expose] noncomputable def conjι (g : X) : MB →* X :=
  (MulAut.conj g).toMonoidHom.comp B.ι

@[expose] def ActsR1 (g : X) (f : List MB) : Prop :=
  ∀ x : MB, MB.inR1 x = true → g * B.ι x * g⁻¹ = B.ι (MB.applyR1 f x)

@[expose] def ActsMB (g : X) (f : List MB) : Prop :=
  ∀ x : MB, g * B.ι x * g⁻¹ = B.ι (MB.applyMB f x)

@[expose] def ActsQ1 (g : X) (f : List MB) : Prop :=
  ∀ x : MB, MB.inQ1 x = true → g * B.ι x * g⁻¹ = B.ι (MB.applyQ1 f x)

variable {B}

theorem actsR1_of_map {g : X} {f : List MB}
    (h : MB.gensR1.map (fun a => g * B.ι a * g⁻¹) = f.map B.ι) : B.ActsR1 g f := by
  intro x hx
  have key : g * B.ι x * g⁻¹ =
      nfProd (MB.gensR1.map (fun a => g * B.ι a * g⁻¹)) (MB.bitsR1 x) := by
    conv_lhs => rw [MB.nf_R1 hx]
    exact map_nfProd (B.conjι g) _ _
  rw [key, h]
  exact (map_nfProd B.ι f (MB.bitsR1 x)).symm

theorem actsQ1_of_map {g : X} {f : List MB}
    (h : MB.gensQ1.map (fun a => g * B.ι a * g⁻¹) = f.map B.ι) : B.ActsQ1 g f := by
  intro x hx
  have key : g * B.ι x * g⁻¹ =
      nfProd (MB.gensQ1.map (fun a => g * B.ι a * g⁻¹)) (MB.bitsQ1 x) := by
    conv_lhs => rw [MB.nf_Q1 hx]
    exact map_nfProd (B.conjι g) _ _
  rw [key, h]
  exact (map_nfProd B.ι f (MB.bitsQ1 x)).symm

theorem actsMB_of_map {g : X} {f : List MB}
    (h : MB.gens.map (fun a => g * B.ι a * g⁻¹) = f.map B.ι) : B.ActsMB g f := by
  intro x
  have key : g * B.ι x * g⁻¹ = nfProd (MB.gens.map (fun a => g * B.ι a * g⁻¹)) (MB.nfBits x) := by
    conv_lhs => rw [MB.nf_spec x]
    exact map_nfProd (B.conjι g) _ _
  rw [key, h]
  exact (map_nfProd B.ι f (MB.nfBits x)).symm

theorem ActsMB.mul {g h : X} {f f' : List MB} (hg : B.ActsMB g f) (hh : B.ActsMB h f') :
    B.ActsMB (g * h) (MB.compMB f f') := by
  intro x
  rw [show g * h * B.ι x * (g * h)⁻¹ = g * (h * B.ι x * h⁻¹) * g⁻¹ by group, hh x]
  have e1 : g * B.ι (MB.applyMB f' x) * g⁻¹ =
      nfProd (f'.map (fun a => g * B.ι a * g⁻¹)) (MB.nfBits x) :=
    map_nfProd (B.conjι g) f' (MB.nfBits x)
  have e2 : B.ι (MB.applyMB (MB.compMB f f') x) =
      nfProd ((f'.map (MB.applyMB f)).map B.ι) (MB.nfBits x) :=
    map_nfProd B.ι (f'.map (MB.applyMB f)) (MB.nfBits x)
  rw [e1, e2, List.map_map]
  congr 1
  exact List.map_congr_left fun y _ => hg y

theorem actsMB_ι (s : MB) : B.ActsMB (B.ι s) (MB.conjMB s) :=
  actsMB_of_map (by simp [MB.conjMB, List.map_map, Function.comp_def, map_mul, map_inv])

theorem actsR1_ι (s : MB) : B.ActsR1 (B.ι s) (MB.conjR1 s) :=
  actsR1_of_map (by simp [MB.conjR1, List.map_map, Function.comp_def, map_mul, map_inv])

theorem actsQ1_ι (s : MB) : B.ActsQ1 (B.ι s) (MB.conjQ1 s) :=
  actsQ1_of_map (by simp [MB.conjQ1, List.map_map, Function.comp_def, map_mul, map_inv])

theorem ActsR1.mul {g h : X} {f f' : List MB} (hg : B.ActsR1 g f) (hh : B.ActsR1 h f')
    (hf' : ∀ y ∈ f', MB.inR1 y = true) : B.ActsR1 (g * h) (MB.compR1 f f') := by
  intro x hx
  rw [show g * h * B.ι x * (g * h)⁻¹ = g * (h * B.ι x * h⁻¹) * g⁻¹ by group, hh x hx]
  have e1 : g * B.ι (MB.applyR1 f' x) * g⁻¹ =
      nfProd (f'.map (fun a => g * B.ι a * g⁻¹)) (MB.bitsR1 x) :=
    map_nfProd (B.conjι g) f' (MB.bitsR1 x)
  have e2 : B.ι (MB.applyR1 (MB.compR1 f f') x) =
      nfProd ((f'.map (MB.applyR1 f)).map B.ι) (MB.bitsR1 x) :=
    map_nfProd B.ι (f'.map (MB.applyR1 f)) (MB.bitsR1 x)
  rw [e1, e2, List.map_map]
  congr 1
  exact List.map_congr_left fun y hy => hg y (hf' y hy)

theorem ActsQ1.mul {g h : X} {f f' : List MB} (hg : B.ActsQ1 g f) (hh : B.ActsQ1 h f')
    (hf' : ∀ y ∈ f', MB.inQ1 y = true) : B.ActsQ1 (g * h) (MB.compQ1 f f') := by
  intro x hx
  rw [show g * h * B.ι x * (g * h)⁻¹ = g * (h * B.ι x * h⁻¹) * g⁻¹ by group, hh x hx]
  have e1 : g * B.ι (MB.applyQ1 f' x) * g⁻¹ =
      nfProd (f'.map (fun a => g * B.ι a * g⁻¹)) (MB.bitsQ1 x) :=
    map_nfProd (B.conjι g) f' (MB.bitsQ1 x)
  have e2 : B.ι (MB.applyQ1 (MB.compQ1 f f') x) =
      nfProd ((f'.map (MB.applyQ1 f)).map B.ι) (MB.bitsQ1 x) :=
    map_nfProd B.ι (f'.map (MB.applyQ1 f)) (MB.bitsQ1 x)
  rw [e1, e2, List.map_map]
  congr 1
  exact List.map_congr_left fun y hy => hg y (hf' y hy)

theorem ActsQ1.actsAs {g : X} {s : MB} (hg : B.ActsQ1 g (MB.conjQ1 s)) :
    ActsAs B.Q1 g (B.ι s) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hg x hx, (actsQ1_ι s) x hx]

theorem ActsR1.eq_of_actsAs {g h : X} {f f' : List MB} (hg : B.ActsR1 g f) (hh : B.ActsR1 h f')
    (hgh : ActsAs B.R1 g h) : ∀ x : MB, MB.inR1 x = true → MB.applyR1 f x = MB.applyR1 f' x :=
  fun x hx => B.ι_injective (by rw [← hg x hx, ← hh x hx, hgh _ ⟨x, hx, rfl⟩])

theorem ActsQ1.eq_of_actsAs {g h : X} {f f' : List MB} (hg : B.ActsQ1 g f) (hh : B.ActsQ1 h f')
    (hgh : ActsAs B.Q1 g h) : ∀ x : MB, MB.inQ1 x = true → MB.applyQ1 f x = MB.applyQ1 f' x :=
  fun x hx => B.ι_injective (by rw [← hg x hx, ← hh x hx, hgh _ ⟨x, hx, rfl⟩])

theorem ActsR1.mem_normalizer {g : X} {f : List MB} (hg : B.ActsR1 g f)
    (hf : ∀ y ∈ f, MB.inR1 y = true) : g ∈ normalizer (B.R1 : Set X) := by
  refine mem_normalizer_of_conj_le fun _ ⟨x, hx, hxe⟩ => ?_
  rw [← hxe, hg x hx]
  exact ⟨_, nfProd_mem (H := MB.R1h) f _ hf, rfl⟩

theorem ActsQ1.mem_normalizer {g : X} {f : List MB} (hg : B.ActsQ1 g f)
    (hf : ∀ y ∈ f, MB.inQ1 y = true) : g ∈ normalizer (B.Q1 : Set X) := by
  refine mem_normalizer_of_conj_le fun _ ⟨x, hx, hxe⟩ => ?_
  rw [← hxe, hg x hx]
  exact ⟨_, nfProd_mem (H := MB.Q1h) f _ hf, rfl⟩

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
