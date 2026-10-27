module

public import CFSG.GH74.GLS.IVK.Proofs2.A7Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Big
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Types

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.A7Fin

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.IVK.A7

section Bridge

variable {K : Type} [Group K]

noncomputable def a7AutA : S7 ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))

noncomputable def a7Aut (ε : K ≃* alternatingGroup (Fin 7)) : S7 ≃* MulAut K :=
  a7AutA.trans (MulAut.congr ε).symm

noncomputable def a7Emb (ε : K ≃* alternatingGroup (Fin 7)) : K →* S7 :=
  (alternatingGroup (Fin 7)).subtype.comp ε.toMonoidHom

theorem a7Emb_injective (ε : K ≃* alternatingGroup (Fin 7)) : Function.Injective (a7Emb ε) := by
  intro x y h
  exact ε.injective (Subtype.ext h)

theorem a7Emb_aut (ε : K ≃* alternatingGroup (Fin 7)) (t : S7) (k : K) :
    a7Emb ε (a7Aut ε t k) = t * a7Emb ε k * t⁻¹ := by
  show ((ε (a7Aut ε t k) : alternatingGroup (Fin 7)) : S7) = t * ((ε k : alternatingGroup (Fin 7)) : S7) * t⁻¹
  have : ε (a7Aut ε t k) = a7AutA t (ε k) := by
    show ε ((MulAut.congr ε).symm (a7AutA t) k) = _
    simp
  rw [this]
  exact MulAut.conjNormal_apply t (ε k)

end Bridge

section Transfer

variable {K : Type} [Group K]

theorem gammaAut_eq_top_of_alt_le (ε : K ≃* alternatingGroup (Fin 7)) {W : Subgroup (MulAut K)}
    (h : alternatingGroup (Fin 7) ≤ Gam7 (W.comap (a7Aut ε).toMonoidHom)) :
    CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Gam7 (W.comap (a7Aut ε).toMonoidHom) ≤
      (CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W).map (a7Emb ε) := by
    refine iSup_le fun t => iSup_le fun ht => iSup_le fun ho => ?_
    intro z hz
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff] at hz
    obtain ⟨hzc, hzA⟩ := hz
    have hzk : a7Emb ε (ε.symm ⟨z, hzA⟩) = z := by simp [a7Emb]
    refine ⟨ε.symm ⟨z, hzA⟩, ?_, hzk⟩
    have hk : (a7Aut ε t) (ε.symm ⟨z, hzA⟩) = ε.symm ⟨z, hzA⟩ := by
      apply a7Emb_injective ε
      rw [a7Emb_aut, hzk]
      calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [← hzc]
        _ = z := by group
    have htW : a7Aut ε t ∈ W := ht
    have hord : orderOf (a7Aut ε t) = 2 :=
      (orderOf_injective (a7Aut ε).toMonoidHom (a7Aut ε).injective t).trans ho
    exact fixedSubgroup_le_gammaAut htW hord hk
  rw [eq_top_iff]
  intro k _
  have hkA : a7Emb ε k ∈ alternatingGroup (Fin 7) := (ε k).2
  obtain ⟨γ, hγ, hγk⟩ := hle (h hkA)
  have : γ = k := a7Emb_injective ε hγk
  rw [← this]
  exact hγ

end Transfer

section Final

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem a7Aut_eq_conj (ε : K ≃* alternatingGroup (Fin 7)) (t : alternatingGroup (Fin 7)) :
    a7Aut ε (t : S7) = MulAut.conj (ε.symm t) := by
  apply MulEquiv.ext
  intro k
  apply ε.injective
  apply Subtype.ext
  show ((ε (a7Aut ε (t : S7) k) : alternatingGroup (Fin 7)) : S7) = _
  have h1 : ε (a7Aut ε (t : S7) k) = a7AutA (t : S7) (ε k) := by
    show ε ((MulAut.congr ε).symm (a7AutA (t : S7)) k) = _
    simp
  rw [h1]
  show ((MulAut.conjNormal (t : S7) (ε k) : alternatingGroup (Fin 7)) : S7) = _
  rw [MulAut.conjNormal_apply]
  simp [MulAut.conj_apply]

theorem b_ivk_6_small_A7 (W : Subgroup (MulAut K))
    (hK : Nonempty (K ≃* alternatingGroup (Fin 7))) (hW2 : IsPGroup 2 ↥W)
    (hWr : 2 ≤ CFSG.pRank 2 ↥W) (hΓ : CFSG.GH74.GLS.C3.Layer1.Bk.gammaAut K W ≠ ⊤) :
    (CFSG.IsElementaryAbelian 2 ↥W ∧ Nat.card ↥W = 4) ∧
      W ≤ (MulAut.conj : K →* MulAut K).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := hK
  have hWr' : 2 ≤ CFSG.Open.pRank 2 W := (TwoThin.pRank_two_subgroup_eq_open W) ▸ hWr
  obtain ⟨E, hEW, hEab, hE4⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hWr'
  have hEsq : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => hEab.2 a ha
  have hE4' : Nat.card ↥E = 4 := by rw [hE4]; norm_num
  obtain ⟨a₀, ha₀, b₀, hb₀, ha₀1, hb₀1, hab₀⟩ :=
    CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hE4'
  have hcomm₀ : a₀ * b₀ = b₀ * a₀ :=
    congrArg Subtype.val (hEab.1.is_comm.comm (⟨a₀, ha₀⟩ : ↥E) ⟨b₀, hb₀⟩)
  set Θ := a7Aut ε with hΘ
  set W₇ : Subgroup S7 := W.comap Θ.toMonoidHom with hW₇
  obtain ⟨a, rfl⟩ := Θ.surjective a₀
  obtain ⟨b, rfl⟩ := Θ.surjective b₀
  have ha : a ∈ W₇ := hEW ha₀
  have hb : b ∈ W₇ := hEW hb₀
  have ha2 : a ^ 2 = 1 := Θ.injective (by rw [map_pow, hEsq _ ha₀, map_one])
  have hb2 : b ^ 2 = 1 := Θ.injective (by rw [map_pow, hEsq _ hb₀, map_one])
  have ha1 : a ≠ 1 := fun h => ha₀1 (by rw [h, map_one])
  have hb1 : b ≠ 1 := fun h => hb₀1 (by rw [h, map_one])
  have hab : a ≠ b := fun h => hab₀ (by rw [h])
  have hcomm : a * b = b * a := Θ.injective (by rw [map_mul, map_mul]; exact hcomm₀)
  have hW₇2 : IsPGroup 2 ↥W₇ := by
    intro g
    obtain ⟨k, hk⟩ := hW2 ⟨Θ g, g.2⟩
    refine ⟨k, Subtype.ext (Θ.injective ?_)⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  have hΓ' : ¬ alternatingGroup (Fin 7) ≤ Gam7 W₇ := fun h => hΓ (gammaAut_eq_top_of_alt_le ε h)
  obtain ⟨hmain1, hmain2⟩ := a7_concrete hW₇2 ha hb ha2 hb2 ha1 hb1 hab hcomm hΓ'
  have hsq : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨t, rfl⟩ := Θ.surjective w
    have := (hmain1 t hw).2
    rw [← map_pow, this, map_one]
  have hcomm' : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    comm_of_sq_eq_one (hsq x hx) (hsq y hy) (hsq _ (W.mul_mem hx hy))
  have hel : CFSG.IsElementaryAbelian 2 ↥W :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 W).2
      ⟨⟨⟨fun x y => Subtype.ext (hcomm' x x.2 y y.2)⟩⟩, hsq⟩
  have hcard : Nat.card ↥W = 4 := by
    have h1 : (W₇.map Θ.toMonoidHom) = W :=
      Subgroup.map_comap_eq_self_of_surjective Θ.surjective W
    rw [← h1, Subgroup.card_map_of_injective Θ.injective]
    exact hmain2
  refine ⟨⟨hel, hcard⟩, ?_⟩
  intro w hw
  obtain ⟨t, rfl⟩ := Θ.surjective w
  have htA : t ∈ alternatingGroup (Fin 7) := (hmain1 t hw).1
  refine ⟨ε.symm ⟨t, htA⟩, ?_⟩
  exact (a7Aut_eq_conj ε ⟨t, htA⟩).symm

end Final

end CFSG.GH74.GLS.IVK.Proofs2.A7Fin
