module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K542Holds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

section Generic

variable {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev SecW (ρ : Representation (ZMod 2) H V) (K : Subgroup H) : Type :=
  ↥(commOn ρ K ⊤) ⧸ K542Proof.subq (commOn ρ K ⊤) (fixOn ρ K (commOn ρ K ⊤))

@[expose] noncomputable def secW (ρ : Representation (ZMod 2) H V) (K : Subgroup H) :
    Representation (ZMod 2) ↥K (SecW ρ K) :=
  K542Proof.secRep (ρ.comp K.subtype) (commOn ρ K ⊤) (fixOn ρ K (commOn ρ K ⊤))
    (fun k _ hu => commOn_top_mapsTo (Subgroup.le_normalizer k.2) hu)
    (fun k c hc => by
      show ρ k c ∈ fixOn ρ K (commOn ρ K ⊤)
      rw [(mem_fixOn.mp hc).2 k k.2]
      exact hc)

theorem secW_mk (ρ : Representation (ZMod 2) H V) (K : Subgroup H) (k : ↥K)
    (u : ↥(commOn ρ K ⊤)) :
    secW ρ K k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨ρ k u, commOn_top_mapsTo (Subgroup.le_normalizer k.2) u.2⟩ :=
  rfl

theorem secW_mk_eq_zero (ρ : Representation (ZMod 2) H V) (K : Subgroup H)
    (u : ↥(commOn ρ K ⊤)) :
    (Submodule.Quotient.mk u : SecW ρ K) = 0 ↔ (u : V) ∈ fixOn ρ K (commOn ρ K ⊤) :=
  Submodule.Quotient.mk_eq_zero _

theorem secW_fixed_eq_zero (ρ : Representation (ZMod 2) H V) (K : Subgroup H)
    [Group.IsPerfect ↥K] (w : SecW ρ K) (hw : ∀ k, secW ρ K k w = w) : w = 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hC : ∀ k : ↥K, ρ k u - u ∈ fixOn ρ K (commOn ρ K ⊤) := fun k => by
    have h := hw k
    rw [secW_mk, Submodule.Quotient.eq] at h
    exact h
  let f : ↥K →* Multiplicative V :=
    { toFun := fun k => Multiplicative.ofAdd (ρ k u - u)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← ofAdd_add]
        congr 1
        have hb : ρ a (ρ b u - u) = ρ b u - u := (mem_fixOn.mp (hC b)).2 a a.2
        rw [map_sub] at hb
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
        calc ρ a (ρ b u) - u = (ρ a (ρ b u) - ρ a u) + (ρ a u - u) := by abel
          _ = (ρ a u - u) + (ρ b u - u) := by rw [hb, add_comm] }
  have h1 : ∀ k : ↥K, ρ k u = u := fun k =>
    sub_eq_zero.mp (ofAdd_eq_one.mp (K542Proof.perfect_hom_eq_one f k))
  exact (secW_mk_eq_zero ρ K u).2 (mem_fixOn.mpr ⟨u.2, fun k hk => h1 ⟨k, hk⟩⟩)

theorem card_secW [Finite V] (ρ : Representation (ZMod 2) H V) (K : Subgroup H) {n : ℕ}
    (hdim : finrank (ZMod 2) ↥(commOn ρ K ⊤) =
      finrank (ZMod 2) ↥(fixOn ρ K (commOn ρ K ⊤)) + n) :
    Nat.card (SecW ρ K) = 2 ^ n := by
  have h := K542Proof.finrank_sec (commOn ρ K ⊤) (fixOn ρ K (commOn ρ K ⊤))
    (fun v hv => (mem_fixOn.mp hv).1)
  have hW : finrank (ZMod 2) (SecW ρ K) = n := by
    unfold SecW
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hW]

end Generic

section Glue

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

variable {X : Type} [Group X] {T : Subgroup X} (hV : CFSG.Open.IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (gnV T) hV))]

theorem card_secW_gnRep [Finite X] (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    (hHI : HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T))
    (hrel : (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ n) :
    Nat.card (SecW (gnRep hV) L) = 2 ^ n :=
  card_secW (gnRep hV) L (K542Proof.clause_to_module hV L hHI hrel).2

end Glue

end CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof
