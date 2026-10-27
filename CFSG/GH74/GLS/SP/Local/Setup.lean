module

public import CFSG.GH74.GLS.SP.Local.Defs
public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open CFSG.GH74.GLS.LU.Local

section Transport

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

theorem SPSyl.transport [Finite G] [Finite Gs] {q : ℕ} (I : CompatIso G z S z' S')
    (hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z)
    (hz' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    {E₁ E₂ : Subgroup Gs} {t' : Gs} (hM : LUComps Gs q z' E₁ E₂)
    (hMS : SPSyl Gs z' S' E₁ E₂ t') :
    ∃ (t : G) (ht : t ∈ layerTimesSylow z (S : Subgroup G)),
      ((I.ψ ⟨t, ht⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = t' ∧
      SPSyl G z S (pull I.ψ E₁) (pull I.ψ E₂) t := by
  set ψ := I.ψ with hψ
  have hz'2 : orderOf z' = 2 := hMS.z_inv
  have hE₁ : E₁ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₁).trans le_sup_left
  have hE₂ : E₂ ≤ layerTimesSylow z' (S' : Subgroup Gs) :=
    (le_layer_of_isCompIn hM.comp₂).trans le_sup_left
  have hzX := z_mem_X hz
  have hψz := I.psi_z hz hz' hz'2
  have hzS : z ∈ (S : Subgroup G) := (mem_of_center_eq hz).1
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_psi ψ hzX, hψz]; exact hz'2
  obtain ⟨t, ht, hψt⟩ := exists_psi_eq ψ (S_le_X _ _ hMS.t_mem)
  have htS : t ∈ (S : Subgroup G) := (I.mem_S ⟨t, ht⟩).mpr (by rw [hψt]; exact hMS.t_mem)
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_psi ψ ht, hψt]; exact hMS.t_ord
  refine ⟨t, ht, hψt, hz2, hz, htS, ht2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pull_map_conj ψ ht, hψt, hMS.t_swap]
  · intro h
    exact hMS.t_nconj
      ((I.fusion ⟨z, hzX⟩ ⟨t, ht⟩ hzS htS hz2 ht2).mp h |> fun h => by rwa [hψz, hψt] at h)
  · have htzX : t * z ∈ layerTimesSylow z (S : Subgroup G) := Subgroup.mul_mem _ ht hzX
    have htzS : t * z ∈ (S : Subgroup G) := Subgroup.mul_mem _ htS hzS
    have hψtz : ((ψ ⟨t * z, htzX⟩ : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs) = t' * z' := by
      rw [psi_mul ψ ht hzX, hψt, hψz]
    have htz2 : orderOf (t * z) = 2 := by
      rw [← orderOf_psi ψ htzX, hψtz, ← orderOf_eq_of_isConj hMS.tz_conj]; exact hz'2
    exact (I.fusion ⟨z, hzX⟩ ⟨t * z, htzX⟩ hzS htzS hz2 htz2).mpr
      (by rw [hψz, hψtz]; exact hMS.tz_conj)
  · intro x hx y hy hx2 hy2 hxz hyz
    have hxK : x ∈ pull ψ (E₁ ⊔ E₂) := by rw [pull_sup ψ hE₁ hE₂]; exact hx
    have hyK : y ∈ pull ψ (E₁ ⊔ E₂) := by rw [pull_sup ψ hE₁ hE₂]; exact hy
    have hxX := pull_le ψ _ hxK
    have hyX := pull_le ψ _ hyK
    have hx' := (mem_pull ψ _ hxX).mp hxK
    have hy' := (mem_pull ψ _ hyX).mp hyK
    obtain ⟨k', hk', hkxy⟩ := hMS.K_one_class _ hx' _ hy'
      (by rw [orderOf_psi ψ hxX]; exact hx2) (by rw [orderOf_psi ψ hyX]; exact hy2)
      (fun h => hxz ((psi_eq_iff ψ hxX hzX).mp (by rw [h, hψz])))
      (fun h => hyz ((psi_eq_iff ψ hyX hzX).mp (by rw [h, hψz])))
    obtain ⟨k, hk, hψk⟩ := exists_psi_eq ψ (hE₁.trans le_rfl |> fun _ => sup_le hE₁ hE₂ hk')
    have hkK : k ∈ pull ψ (E₁ ⊔ E₂) := by rw [mem_pull ψ _ hk, hψk]; exact hk'
    refine ⟨k, by rwa [pull_sup ψ hE₁ hE₂] at hkK, ?_⟩
    have hkinv : k⁻¹ ∈ layerTimesSylow z (S : Subgroup G) := Subgroup.inv_mem _ hk
    have hmul : k * x * k⁻¹ ∈ layerTimesSylow z (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hxX) hkinv
    refine (psi_eq_iff ψ hmul hyX).mp ?_
    have e1 := psi_mul ψ (Subgroup.mul_mem _ hk hxX) hkinv
    have e2 := psi_mul ψ hk hxX
    have e3 := psi_inv ψ hk
    rw [e1, e2, e3, hψk]
    exact hkxy
  · obtain ⟨x', hx', hx'2, hx'z, hx'c⟩ := hMS.K_inv_t
    obtain ⟨x, hx, hψx⟩ := exists_psi_eq ψ (S_le_X _ _ hx'.1)
    have hxS : x ∈ (S : Subgroup G) := (I.mem_S ⟨x, hx⟩).mpr (by rw [hψx]; exact hx'.1)
    have hxK : x ∈ pull ψ (E₁ ⊔ E₂) := by rw [mem_pull ψ _ hx, hψx]; exact hx'.2
    have hx2 : orderOf x = 2 := by rw [← orderOf_psi ψ hx, hψx]; exact hx'2
    refine ⟨x, ⟨hxS, by rwa [pull_sup ψ hE₁ hE₂] at hxK⟩, hx2,
      fun h => hx'z (by
        have h' := (psi_eq_iff ψ hx hzX).mpr h
        rw [hψx, hψz] at h'
        exact h'), ?_⟩
    exact (I.fusion ⟨t, ht⟩ ⟨x, hx⟩ htS hxS ht2 hx2).mpr (by rw [hψt, hψx]; exact hx'c)
  · have hSpull : pull ψ (S' : Subgroup Gs) = (S : Subgroup G) := by
      ext x
      constructor
      · intro h
        have hx := pull_le ψ _ h
        exact (I.mem_S ⟨x, hx⟩).mpr ((mem_pull ψ _ hx).mp h)
      · intro h
        have hx : x ∈ layerTimesSylow z (S : Subgroup G) := S_le_X _ _ h
        exact (mem_pull ψ _ hx).mpr ((I.mem_S ⟨x, hx⟩).mp h)
    have hS'X : (S' : Subgroup Gs) ≤ layerTimesSylow z' (S' : Subgroup Gs) := S_le_X _ _
    have h1 := card_pull ψ hS'X
    have h2 := card_pull ψ (inf_le_left.trans hS'X : (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂) ≤ _)
    rw [hSpull] at h1
    rw [pull_inf, hSpull, pull_sup ψ hE₁ hE₂] at h2
    rw [h1, h2]
    exact hMS.index

end Transport

theorem exists_lieModel_psp {Gs : Type} [Group Gs] {F : Type} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) (hodd : Odd (Nat.card F))
    (e : Nonempty (Gs ≃* StatedProj (StatedSp 2 F))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel Gs .PSp 2 p f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpc⟩ := CharP.exists F
  have hp : p.Prime := CharP.char_is_prime F p
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩))
  refine ⟨p, n, hp, hp2, Or.inl ⟨by simp [classicalTags], ⟨hp, n.pos, le_rfl, ?_⟩, F, inferInstance,
    inferInstance, hcard', e⟩⟩
  intro h
  have : p ^ (n : ℕ) = 2 := (Prod.mk.inj h).2
  omega

theorem spSetupLeaf_of_model (hM : SPModelLeaf) : SPSetupLeaf := by
  intro G _ _ hG Gs _ F _ _ hF hodd e hT
  obtain ⟨-, S, z, S', z', hz, hz', ⟨ψ, hψS, hψfus⟩, hPSp, -⟩ := hT
  let I : CompatIso G z S z' S' := ⟨ψ, hψS, hψfus⟩
  have : Finite Gs := by
    obtain ⟨e'⟩ := e
    exact Finite.of_equiv _ e'.symm.toEquiv
  have hCbot : pPrimeCore 2 ↥(Cz z) = ⊥ := hPSp (exists_lieModel_psp hF hodd e)
  have hA0 : A0 z = ⊥ := by
    show (pPrimeCore 2 ↥(Cz z)).map (Cz z).subtype = ⊥
    rw [hCbot]; exact Subgroup.map_bot _
  have hcyc : IsCyclic ↥(A0 z) := by
    rw [hA0]; infer_instance
  obtain ⟨E₁, E₂, t', d⟩ := hM Gs F hF hodd e S' z' hz'
  have hcomps := LUComps.transport I hz hz' hcyc d.comps d.syl.z_inv
  obtain ⟨t, ht, hψt, hsyl⟩ := SPSyl.transport I hz hz' d.comps d.syl
  exact ⟨z, S, _, _, t, hcomps, hsyl, hA0⟩

end CFSG.GH74.GLS.SP.Local
