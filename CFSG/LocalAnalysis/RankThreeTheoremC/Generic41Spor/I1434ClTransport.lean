module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

section Transport

variable {K M : Type} [Group K] [Group M]

theorem map_conj_zpowers (e : K ≃* M) (x g : K) :
    ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (Subgroup.zpowers (e x)).map (MulAut.conj (e g)).toMonoidHom := by
  have hz : (Subgroup.zpowers x).map e.toMonoidHom = Subgroup.zpowers (e x) :=
    MonoidHom.map_zpowers e.toMonoidHom x
  rw [Subgroup.map_map, ← hz, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem map_symm_map (e : K ≃* M) (S : Subgroup K) :
    (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
    ext y
    simp
  rw [this, Subgroup.map_id]

theorem map_map_symm (e : K ≃* M) (S : Subgroup M) :
    (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
  have := map_symm_map e.symm S
  simpa using this

theorem ncard_conj_map (e : K ≃* M) (x : K) (Q : Subgroup K) :
    Set.ncard {B : Subgroup M | ∃ g : M,
        B = (Subgroup.zpowers (e x)).map (MulAut.conj g).toMonoidHom ∧
          B ≤ Q.map e.toMonoidHom} =
      Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ Q} := by
  have himg : {B : Subgroup M | ∃ g : M,
        B = (Subgroup.zpowers (e x)).map (MulAut.conj g).toMonoidHom ∧
          B ≤ Q.map e.toMonoidHom} =
      (Subgroup.map e.toMonoidHom) '' {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ Q} := by
    ext B
    constructor
    · rintro ⟨g, rfl, hle⟩
      refine ⟨((Subgroup.zpowers (e x)).map (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom,
        ⟨e.symm g, ?_, ?_⟩, map_map_symm e _⟩
      · have h := map_conj_zpowers e.symm (e x) g
        rw [MulEquiv.symm_apply_apply] at h
        exact h
      · calc _ ≤ (Q.map e.toMonoidHom).map e.symm.toMonoidHom := Subgroup.map_mono hle
          _ = Q := map_symm_map e Q
    · rintro ⟨A, ⟨g, rfl, hle⟩, rfl⟩
      exact ⟨e g, map_conj_zpowers e x g, Subgroup.map_mono hle⟩
  rw [himg]
  exact Set.ncard_image_of_injective _ (Subgroup.map_injective e.injective)

theorem exists_sylow_map [Finite K] (e : K ≃* M) (Q : Sylow 5 K) :
    ∃ Q' : Sylow 5 M, (Q' : Subgroup M) = (Q : Subgroup K).map e.toMonoidHom := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q, rfl⟩

theorem transport_lines [Finite K] (e : K ≃* M) (Q : Sylow 5 K) {x : K} (hx : x ∈ (Q : Subgroup K))
    (hd : Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 1 ∨
      Set.ncard {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 3) :
    ∃ Q' : Sylow 5 M, e x ∈ (Q' : Subgroup M) ∧
      (Set.ncard {B : Subgroup M | ∃ g : M,
          B = (Subgroup.zpowers (e x)).map (MulAut.conj g).toMonoidHom ∧
            B ≤ (Q' : Subgroup M)} = 1 ∨
        Set.ncard {B : Subgroup M | ∃ g : M,
          B = (Subgroup.zpowers (e x)).map (MulAut.conj g).toMonoidHom ∧
            B ≤ (Q' : Subgroup M)} = 3) := by
  obtain ⟨Q', hQ'⟩ := exists_sylow_map e Q
  refine ⟨Q', by rw [hQ']; exact ⟨x, hx, rfl⟩, ?_⟩
  rw [hQ', ncard_conj_map e x (Q : Subgroup K)]
  exact hd

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
