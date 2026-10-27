module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenA
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NineB

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open Equiv.Perm (viaEmbeddingHom)
open scoped commutatorElement

section CaseB

variable {V : Type} [CommGroup V] [Finite V] {G T Y L : Subgroup (MulAut V)} {t : MulAut V}

theorem TenCfg.false_of_five (hc : TenCfg G T Y t L) (A : TenAlt L Y 5) : False := by
  classical
  obtain ⟨ι, hcι⟩ : ∃ ι : Fin 5 ↪ Fin 5,
      (A.c : Equiv.Perm (Fin 5)) = viaEmbeddingHom ι (Equiv.swap 0 1 * Equiv.swap 1 2) :=
    exists_embedding_threeCycle (k := 2) (by omega) A.c3
  obtain ⟨hf1, hf2⟩ := caseB_perm_facts
  set E := viaEmbeddingHom ι with hE
  have hρ_alt : E (Equiv.swap 1 3 * Equiv.swap 2 4) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_viaEmbeddingHom]; exact hf2
  obtain ⟨xρ, hxρ⟩ := A.exists_lift hρ_alt
  obtain ⟨y0, hy0Y, hy0c⟩ := A.exists_y
  have hYG : Y ≤ G := fun y hy => (hc.cfg.adm.hYC hy).1
  have hx₂ε : A.eps (lpi L (xρ * y0 * xρ⁻¹)) =
      E (Equiv.swap 0 3 * Equiv.swap 3 4) := by
    simp only [map_mul, map_inv]
    rw [hxρ, hy0c, hcι, ← map_inv, ← map_mul, ← map_mul, hf1]
    exact map_mul E _ _
  set J : Subgroup (MulAut V) := CGT6E.conjSub (xρ : MulAut V) Y ⊔ Y with hJ
  have hyJ : (y0 : MulAut V) ∈ J := Subgroup.mem_sup_right hy0Y
  have hx₂J : ((xρ * y0 * xρ⁻¹ : ↥L) : MulAut V) ∈ J :=
    Subgroup.mem_sup_left (CGT6E.conj_mem_conjSub hy0Y)
  have hclosure : Subgroup.closure {(A.c : Equiv.Perm (Fin 5)),
      E (Equiv.swap 0 3 * Equiv.swap 3 4)} = alternatingGroup (Fin 5) := by
    have h1 := MonoidHom.map_closure E {Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2,
      Equiv.swap 0 3 * Equiv.swap 3 4}
    rw [Set.image_pair] at h1
    rw [hcι, ← h1, closure_std_five, map_viaEmbeddingHom_eq_alt]
  have htop : tilde (L := L) J = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have hs : A.eps s ∈ alternatingGroup (Fin 5) := (A.e s).2
    rw [← hclosure] at hs
    have hsub : Subgroup.closure {(A.c : Equiv.Perm (Fin 5)),
        E (Equiv.swap 0 3 * Equiv.swap 3 4)} ≤ (tilde (L := L) J).map A.eps := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨lpi L y0, mem_tilde.mpr ⟨y0, y0.2, hyJ, rfl⟩, hy0c⟩
      · exact ⟨lpi L (xρ * y0 * xρ⁻¹), mem_tilde.mpr ⟨_, (xρ * y0 * xρ⁻¹).2, hx₂J, rfl⟩, hx₂ε⟩
    obtain ⟨s', hs', hss'⟩ := hsub hs
    have : s' = s := A.eps_injective hss'
    rw [← this]
    exact hs'
  have hLJ : L ≤ J := le_of_tilde_eq_top hc.layer.quasi.1 htop
  have hxG : (xρ : MulAut V) ∈ G := hc.layer.le xρ.2
  have htG : t ∈ G := hc.ht.1
  have hKG : CGT6E.conjSub (xρ : MulAut V) Y ⊔ Y ⊔ Subgroup.zpowers t ≤ G :=
    sup_le (sup_le (conjSub_le_of_mem hxG hYG) hYG) (Subgroup.zpowers_le.mpr htG)
  have hNK : conjClosure Y G ≤ CGT6E.conjSub (xρ : MulAut V) Y ⊔ Y ⊔ Subgroup.zpowers t :=
    (hc.layer.conjClosure_eq hc.hYL).le.trans (hLJ.trans le_sup_left)
  have hKeq := hc.cfg.eq_of_conjClosure_le hc.hV hc.ht hc.ht1 hc.ht2 hNK hKG
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  exact hc.hforall _ hxG hKeq

end CaseB

end CFSG.CGT.PushingUpLit.CGT6
