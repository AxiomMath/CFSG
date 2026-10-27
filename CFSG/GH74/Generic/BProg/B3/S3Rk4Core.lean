module

public import CFSG.GH74.Generic.BProg.B3.S3Rk4KGrp
public import CFSG.GH74.Generic.BProg.B3.S3Rk4Layer
public import CFSG.GH74.Generic.BProg.B3.S3Rk3B

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk4Core

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.Generic.BProg
  CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_conj_pair {x y y' x' w : G} (hw1 : w * x' * w⁻¹ = x) (hw2 : w * y * w⁻¹ = y')
    {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)) I) :
    IsPCompIn 2 (centralizer ({x'} : Set G) ⊓ centralizer ({y} : Set G))
      (I.map (MulAut.conj w⁻¹).toMonoidHom) := by
  have h := GLS.Stage1.Thm2.Recip.isPCompIn_map_conj hI w⁻¹
  have hX : (centralizer ({x} : Set G) ⊓ centralizer ({y'} : Set G)).map
      (MulAut.conj w⁻¹).toMonoidHom = centralizer ({x'} : Set G) ⊓ centralizer ({y} : Set G) := by
    have hinj : Function.Injective ((MulAut.conj w⁻¹).toMonoidHom) := (MulAut.conj w⁻¹).injective
    rw [Subgroup.map_inf _ _ _ hinj, GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj,
      GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj]
    have e1 : w⁻¹ * x * w⁻¹⁻¹ = x' := by rw [← hw1]; group
    have e2 : w⁻¹ * y' * w⁻¹⁻¹ = y := by rw [← hw2]; group
    rw [e1, e2]
  rwa [hX] at h

omit [Finite G] in
theorem conj_pair {a b : G} (g : G) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a) :
    (g * a * g⁻¹) * (g * a * g⁻¹) = 1 ∧ (g * b * g⁻¹) * (g * b * g⁻¹) = 1 ∧ g * a * g⁻¹ ≠ 1 ∧
      g * b * g⁻¹ ≠ 1 ∧ g * a * g⁻¹ ≠ g * b * g⁻¹ ∧
      (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  · calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  · intro e
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · intro e
    apply hb1
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · intro e
    apply hab
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [e]
      _ = b := by group
  · calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hc]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem core {x y y' x' w : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hbar : barSub y (pumpUp 2 (Ly K y) y) = barSub y (Ly K y))
    (hy'2 : y' * y' = 1) (hxy' : x * y' = y' * x) (hx'x : x' * x = x * x')
    (hx'y : x' * y = y * x') (hx'2 : x' * x' = 1) (hw1 : w * x' * w⁻¹ = x)
    (hw2 : w * y * w⁻¹ = y') (hw3 : w * x * w⁻¹ = x * y) (hout : y' ∉ K ⊔ CxK x K) : False := by
  classical
  have hx : orderOf x = 2 := S3L3Facts.ord_x h
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := fun e => by simp [e] at hx
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3L3Facts.pcomp h
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hyK : y ∈ K := S3L3Facts.y_mem_K h
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.1 (hKC hyK)).symm
  obtain ⟨E, -, -, -, -, -, hxK⟩ := S3Rk1Basic.exists_E h.circ h.src h.shape
  have hxCxK : x ∈ CxK x K := S3Rk3B.x_mem_CxK (cfg_of_setup30 h hT)
  obtain ⟨I, hIcomp, hIK, a, b, haI, hbI, ha2, hb2, ha1, hb1, hab, hcomm⟩ :=
    S3Rk4KGrp.exists_I h hT hy'2 hxy' hout
  set I' : Subgroup G := I.map (MulAut.conj w⁻¹).toMonoidHom
  have hI' : IsPCompIn 2 (centralizer ({x'} : Set G) ⊓ centralizer ({y} : Set G)) I' :=
    isPCompIn_conj_pair hw1 hw2 hIcomp
  have hxW : x ∈ centralizer ({x'} : Set G) ⊓ centralizer ({y} : Set G) :=
    Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hx'x.symm, mem_centralizer_singleton_iff.2 hxy⟩
  set I'' : Subgroup G := I'.map (MulAut.conj x).toMonoidHom
  have hI'' : IsPCompIn 2 (centralizer ({x'} : Set G) ⊓ centralizer ({y} : Set G)) I'' :=
    FalseCtxS45Comp.isPCompIn_conj hI' hxW
  have hH := (thm9_l3_rank1 h).1
  have hty : x' ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.2 hx'y
  have hx'1 : x' ≠ 1 := by
    intro e
    apply hx1
    rw [← hw1, e]
    group
  have hx'ord : orderOf x' = 2 := orderOf_eq_prime (by rw [sq]; exact hx'2) hx'1
  have htH := S3Rk4Layer.mem_normalizer_pumpUp h hH hbar hty hx'x
  have hG4 : Gen4 G := h.hyp.gen4
  obtain ⟨c2, d2, c1, d1, cd1, cm⟩ := conj_pair w⁻¹ ha2 hb2 ha1 hb1 hab hcomm
  have haI' : w⁻¹ * a * w⁻¹⁻¹ ∈ I' := ⟨a, haI, rfl⟩
  have hbI' : w⁻¹ * b * w⁻¹⁻¹ ∈ I' := ⟨b, hbI, rfl⟩
  obtain ⟨c2', d2', c1', d1', cd1', cm'⟩ := conj_pair x c2 d2 c1 d1 cd1 cm
  have haI'' : x * (w⁻¹ * a * w⁻¹⁻¹) * x⁻¹ ∈ I'' := ⟨_, haI', rfl⟩
  have hbI'' : x * (w⁻¹ * b * w⁻¹⁻¹) * x⁻¹ ∈ I'' := ⟨_, hbI', rfl⟩
  have hI'y : I' ≤ centralizer ({y} : Set G) := hI'.1.trans inf_le_right
  have hI''y : I'' ≤ centralizer ({y} : Set G) := hI''.1.trans inf_le_right
  have hnot1 : ¬ barSub y I' ≤ barSub y (pumpUp 2 (Ly K y) y) :=
    S3Rk4Layer.not_bar_le h hbar hI'y haI' hbI' c2 d2 c1 d1 cd1 cm
  have hnot2 : ¬ barSub y I'' ≤ barSub y (pumpUp 2 (Ly K y) y) :=
    S3Rk4Layer.not_bar_le h hbar hI''y haI'' hbI'' c2' d2' c1' d1' cd1' cm'
  have hcs1 := S3Rk4Layer.le_cSec_of_stable hG4 hty hx'ord hH htH hI' hnot1
  have hcs2 := S3Rk4Layer.le_cSec_of_stable hG4 hty hx'ord hH htH hI'' hnot2
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = I' ⊔ I'' := ⟨_, rfl⟩
  have hMcs : M ≤ centralizerSection (pumpUp 2 (Ly K y) y)
      (pPrimeCoreOf 2 (pumpUp 2 (Ly K y) y)) := by
    rw [hMdef]
    exact sup_le hcs1 hcs2
  have hMy : M ≤ centralizer ({y} : Set G) := by
    rw [hMdef]
    exact sup_le hI'y hI''y
  have hMx : ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    have hle : M ≤ M.comap (MulAut.conj x).toMonoidHom := by
      rw [hMdef]
      refine sup_le ?_ ?_
      · intro m hm
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right ⟨m, hm, rfl⟩)
      · rintro _ ⟨m, hm, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        show x * (x * m * x⁻¹) * x⁻¹ ∈ I' ⊔ I''
        have : x * (x * m * x⁻¹) * x⁻¹ = m := by
          calc x * (x * m * x⁻¹) * x⁻¹ = (x * x) * m * (x * x)⁻¹ := by group
            _ = m := by rw [hx2]; group
        rw [this]
        exact Subgroup.mem_sup_left hm
    exact fun m hm => hle hm
  have hMeven : 2 ∣ Nat.card ↥M := by
    have haM : w⁻¹ * a * w⁻¹⁻¹ ∈ M := by
      rw [hMdef]
      exact Subgroup.mem_sup_left haI'
    have hord : orderOf (⟨w⁻¹ * a * w⁻¹⁻¹, haM⟩ : ↥M) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [sq]; exact c2) c1
    have := orderOf_dvd_natCard (⟨w⁻¹ * a * w⁻¹⁻¹, haM⟩ : ↥M)
    rwa [hord] at this
  have hMK : ∀ m ∈ M, w * m * w⁻¹ ∈ K := by
    have hle : M ≤ K.comap (MulAut.conj w).toMonoidHom := by
      rw [hMdef]
      refine sup_le ?_ ?_
      · rintro _ ⟨i, hi, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        show w * (w⁻¹ * i * w⁻¹⁻¹) * w⁻¹ ∈ K
        have : w * (w⁻¹ * i * w⁻¹⁻¹) * w⁻¹ = i := by group
        rw [this]
        exact hIK hi
      · rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        show w * (x * (w⁻¹ * i * w⁻¹⁻¹) * x⁻¹) * w⁻¹ ∈ K
        have hyiK : y * i * y⁻¹ ∈ K := K.mul_mem (K.mul_mem hyK (hIK hi)) (K.inv_mem hyK)
        have hc : x * (y * i * y⁻¹) = (y * i * y⁻¹) * x :=
          (mem_centralizer_singleton_iff.1 (hKC hyiK)).symm
        have e1 : w * (x * (w⁻¹ * i * w⁻¹⁻¹) * x⁻¹) * w⁻¹ = (x * y) * i * (x * y)⁻¹ := by
          rw [← hw3]; group
        rw [e1]
        have e2 : (x * y) * i * (x * y)⁻¹ = (x * (y * i * y⁻¹)) * x⁻¹ := by group
        rw [e2, hc]
        have e3 : (y * i * y⁻¹) * x * x⁻¹ = y * i * y⁻¹ := by group
        rw [e3]
        exact hyiK
    exact fun m hm => hle hm
  obtain ⟨v, hvM, hv2, hv1, hxv⟩ := S3Rk4Basic.exists_comm_involution hx2 hMx hMeven
  have hvC : v ∈ CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.2 ⟨hMy hvM, hMcs hvM⟩ : v ∈ CxK y (pumpUp 2 (Ly K y) y)),
      mem_centralizer_singleton_iff.2 hxv.symm⟩
  have hvK := hMK v hvM
  rcases (prop305 h).2 v hvC hv2 with e | e | e | e
  · exact hv1 e
  ·
    rw [e, hw3] at hvK
    exact hxK (by simpa using K.mul_mem hvK (K.inv_mem hyK))
  ·
    rw [e, hw2] at hvK
    exact hout (Subgroup.mem_sup_left hvK)
  ·
    have e' : w * v * w⁻¹ = (x * y) * y' := by
      rw [e]
      calc w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
        _ = (x * y) * y' := by rw [hw3, hw2]
    rw [e'] at hvK
    apply hout
    have hxyKC : x * y ∈ K ⊔ CxK x K :=
      (K ⊔ CxK x K).mul_mem (Subgroup.mem_sup_right hxCxK) (Subgroup.mem_sup_left hyK)
    have : y' = (x * y)⁻¹ * ((x * y) * y') := by group
    rw [this]
    exact (K ⊔ CxK x K).mul_mem ((K ⊔ CxK x K).inv_mem hxyKC) (Subgroup.mem_sup_left hvK)

end S3Rk4Core

end CFSG.GH74.Generic.BProg.B3
