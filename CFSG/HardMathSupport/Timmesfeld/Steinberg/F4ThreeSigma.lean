module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeKernelSizes

public section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def f4SigmaCertF4 : ComponentCert where
  lab :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  mid :=
    [0, 1, 1, 7, 4, 5, 6, 7, 8, 1, 1, 7, 12, 13, 14, 15, 16, 17, 18, 1, 20, 1, 22, 23, 24, 25,
     26, 27, 1, 29, 1, 31, 32, 33, 1, 1, 1, 37, 1, 39, 7, 1, 42, 43, 15, 7, 46, 15]

theorem f4SigmaCertF4_check :
    f4SigmaCertF4.check .F4 (triIn (vec3 (τ := .F4) [0, 0, 0, 0])) = true := by
  decide +kernel

theorem f4_kernelSizes_F4 :
    KernelSizes (triChar (vec3 (τ := .F4) [0, 0, 0, 0])) [48] :=
  (kernelSizes_triChar _ _ f4SigmaCertF4_check).of_perm (by decide +kernel)

@[expose] def f4SigmaCertC3 : ComponentCert where
  lab :=
    [0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  mid :=
    [0, 1, 2, 2, 4, 5, 6, 2, 8, 9, 10, 2, 12, 13, 2, 10, 16, 17, 18, 19, 20, 21, 22, 10, 24, 2,
     26, 27, 28, 29, 30, 31, 32, 2, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

theorem f4SigmaCertC3_check :
    f4SigmaCertC3.check .F4 (triIn (vec3 (τ := .F4) [1, 0, 0, 0])) = true := by
  decide +kernel

theorem f4_kernelSizes_C3 :
    KernelSizes (triChar (vec3 (τ := .F4) [1, 0, 0, 0])) [18] :=
  (kernelSizes_triChar _ _ f4SigmaCertC3_check).of_perm (by decide +kernel)

@[expose] def f4SigmaCertA2A2t : ComponentCert where
  lab :=
    [0, 0, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  mid :=
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
     25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

theorem f4SigmaCertA2A2t_check :
    f4SigmaCertA2A2t.check .F4 (triIn (vec3 (τ := .F4) [0, 1, 0, 0])) = true := by
  decide +kernel

theorem f4_kernelSizes_A2A2t :
    KernelSizes (triChar (vec3 (τ := .F4) [0, 1, 0, 0])) [6, 6] :=
  (kernelSizes_triChar _ _ f4SigmaCertA2A2t_check).of_perm (by decide +kernel)

@[expose] def f4SigmaCertB3 : ComponentCert where
  lab :=
    [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1,
     1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0]
  mid :=
    [0, 1, 2, 13, 4, 5, 6, 7, 8, 9, 10, 13, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
     25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 13, 44, 45, 13, 47]

theorem f4SigmaCertB3_check :
    f4SigmaCertB3.check .F4 (triIn (vec3 (τ := .F4) [1, 0, 1, 0])) = true := by
  decide +kernel

theorem f4_kernelSizes_B3 :
    KernelSizes (triChar (vec3 (τ := .F4) [1, 0, 1, 0])) [18] :=
  (kernelSizes_triChar _ _ f4SigmaCertB3_check).of_perm (by decide +kernel)

end CFSG.HardMathSupport.Timmesfeld.Steinberg
