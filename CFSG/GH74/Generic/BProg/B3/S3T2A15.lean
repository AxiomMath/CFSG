module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A15

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem center_alt11_eq_bot : center (alternatingGroup (Fin 11)) = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 11)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 11))) with h | h
  · exact h
  · exfalso
    let u : alternatingGroup (Fin 11) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      rfl⟩
    let v : alternatingGroup (Fin 11) := ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      rfl⟩
    have hu : u ∈ center (alternatingGroup (Fin 11)) := h ▸ Subgroup.mem_top u
    have huv : v * u = u * v := Subgroup.mem_center_iff.mp hu v
    have hne : (v * u : alternatingGroup (Fin 11)) ≠ u * v := by
      intro heq
      have := congrArg (fun g : alternatingGroup (Fin 11) => (g : Equiv.Perm (Fin 11)) 0) heq
      revert this
      decide
    exact hne huv

variable {G : Type} [Group G] [Finite G]

theorem noA11 (hG : Gen4 G) {t : G} {J : Subgroup G} (hJ : IsILo 2 t J) :
    IsEmpty (kBar J ≃* alternatingGroup (Fin 11)) := by
  refine ⟨fun e => ?_⟩
  set L : Subgroup (CentralizerBar t) :=
    (J.subgroupOf (centralizer ({t} : Set G))).map (Th2.Bal.piBar t) with hL
  obtain ⟨e'⟩ := Th2.Bal.kBar_equiv_of_over hJ.2.2 hL.symm
  let φ : alternatingGroup (Fin 11) ≃* ↥L := e.symm.trans e'
  have hc : center ↥L = ⊥ := by
    rw [← Subgroup.map_center_eq φ, center_alt11_eq_bot, Subgroup.map_bot]
  have hxL := xbar_not_mem_of_center_eq_bot hJ.1 hc
  exact not_rankCertified_three_of_xbar_not_mem hG hJ.1 hxL
    ((rankCertified_alternating (by norm_num : 8 ≤ 11)).of_mulEquiv φ)

@[expose] def CenterA11 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → ∀ (t : G) (J : Subgroup G), IsILo 2 t J →
      Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 11)) → center (kBar J) = ⊥

@[expose] def CenterA7 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → ∀ (t : G) (J : Subgroup G), IsILo 2 t J →
      Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 7)) → center (kBar J) = ⊥

theorem hyp15A7_of (hG : Gen4 G)
    (h11 : ∀ (t : G) (J : Subgroup G), IsILo 2 t J →
      Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 11)) → center (kBar J) = ⊥)
    (h7 : ∀ (t : G) (J : Subgroup G), IsILo 2 t J →
      Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 7)) → center (kBar J) = ⊥) :
    Hyp15A7 G := by
  intro t J hJ
  refine ⟨⟨fun e => ?_⟩, h7 t J hJ⟩
  have hZ := h11 t J hJ ⟨e⟩
  exact (noA11 hG hJ).false (QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).symm.trans e))

theorem l15A7_of (h11 : CenterA11 G) (h7 : CenterA7 G) :
    ∀ (x : G) (K A : Subgroup G) (a : G) (D J : Subgroup G), Ctx21 G x K A a D J →
      QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → Hyp15A7 G := fun x K _ _ _ _ hc h3 =>
  hyp15A7_of hc.hyp.gen4 (h11 x K hc.hyp hc.noAlt hc.circ h3) (h7 x K hc.hyp hc.noAlt hc.circ h3)

end CFSG.GH74.Generic.BProg.B3.S3T2A15
