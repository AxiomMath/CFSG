module

public import CFSG.LieType.SpecialLinear.Block222.Borel.BlockEmbedProof

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis

noncomputable section

variable (c : ℕ) (F : Type) [Field F] (A : GL (Fin (c + 4)) F)
  (σ : F ≃+* F) (ε : ℕ)

theorem block222_intertwine_apply (hA : IsUpperGL A) {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k (SpecialLinearGroup (Fin (c + 4)) F) V) (T : V →ₗ[k] V)
    (hT : ∀ g v, T (ρ g v) = ρ (borelStd (c + 4) F A σ ε g) (T v)) :
    (∀ x ∈ fixSub ρ (blockRadical222 c F), T x ∈ fixSub ρ (blockRadical222 c F)) ∧
      ∀ g, ∀ x ∈ fixSub ρ (blockRadical222 c F),
        T (ρ (blockEmbed222 c F g) x) =
          ρ (blockEmbed222 c F (blockStd222 c F A hA σ ε g)) (T x) := by
  have hN : (blockRadical222 c F).map (borelStd (c + 4) F A σ ε).toMonoidHom =
      blockRadical222 c F :=
    blockRadical222_map_borelStd c F A hA σ ε
  have hfix : ∀ x ∈ fixSub ρ (blockRadical222 c F),
      T x ∈ fixSub ρ (blockRadical222 c F) :=
    fixSub_mapsTo_of_intertwine hN hT
  refine ⟨hfix, ?_⟩
  intro g x hx
  have hTx : T x ∈ fixSub ρ (blockRadical222 c F) := hfix x hx
  let q : SpecialLinearGroup (Fin (c + 4)) F :=
    (blockEmbed222 c F (blockStd222 c F A hA σ ε g))⁻¹ *
      borelStd (c + 4) F A σ ε (blockEmbed222 c F g)
  have hq : q ∈ blockRadical222 c F :=
    borelStd_blockEmbed222 c F A hA σ ε g
  have hdecomp : borelStd (c + 4) F A σ ε (blockEmbed222 c F g) =
      blockEmbed222 c F (blockStd222 c F A hA σ ε g) * q := by
    rw [show q = (blockEmbed222 c F (blockStd222 c F A hA σ ε g))⁻¹ *
        borelStd (c + 4) F A σ ε (blockEmbed222 c F g) from rfl]
    group
  calc T (ρ (blockEmbed222 c F g) x)
      = ρ (borelStd (c + 4) F A σ ε (blockEmbed222 c F g)) (T x) := hT _ _
    _ = ρ (blockEmbed222 c F (blockStd222 c F A hA σ ε g) * q) (T x) := by rw [hdecomp]
    _ = ρ (blockEmbed222 c F (blockStd222 c F A hA σ ε g)) (ρ q (T x)) := by
        rw [map_mul]
        rfl
    _ = ρ (blockEmbed222 c F (blockStd222 c F A hA σ ε g)) (T x) := by
        congr 1
        exact (mem_fixSub (ρ := ρ) (S := blockRadical222 c F)).mp hTx q hq

end

end CFSG.LieType.SpecialLinear
