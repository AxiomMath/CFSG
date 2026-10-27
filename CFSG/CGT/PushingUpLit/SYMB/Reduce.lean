module

public import CFSG.CGT.PushingUpLit.SYMB.Setting

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

theorem sym_Q_sylow (S : SymSetting G T V n φ ψ T') :
    IsSylowTwoOf (T ⊓ kerG G φ) (kerG G φ) :=
  B6.isSylowTwoOf_inf_normal S.sylow (fun _ hg => (mem_kerG.1 hg).1) (le_normalizer_kerG G φ)

theorem sym_frattini (S : SymSetting G T V n φ ψ T') :
    G ≤ kerG G φ ⊔ (G ⊓ Subgroup.normalizer ((T ⊓ kerG G φ : Subgroup Γ) : Set Γ)) :=
  B6.frattini_two (fun _ hg => (mem_kerG.1 hg).1) (le_normalizer_kerG G φ) (sym_Q_sylow S)

theorem sym_Q_normal_of_no_L (S : SymSetting G T V n φ ψ T')
    (hno : ∀ L ∈ lSet G T, imgG G φ L ≠ ⊤) :
    G ≤ Subgroup.normalizer ((T ⊓ kerG G φ : Subgroup Γ) : Set Γ) := by
  classical
  set Q : Subgroup Γ := T ⊓ kerG G φ with hQ
  set L : Subgroup Γ := G ⊓ Subgroup.normalizer (Q : Set Γ) with hLdef
  have hLG : L ≤ G := inf_le_left
  have hKG : kerG G φ ≤ G := fun _ hg => (mem_kerG.1 hg).1
  have hTL : T ≤ L := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨S.sylow.1 ht, ?_⟩
    have htG : t ∈ G := S.sylow.1 ht
    have hkn : t ∈ Subgroup.normalizer (kerG G φ : Set Γ) := le_normalizer_kerG G φ htG
    have htn : t ∈ Subgroup.normalizer (T : Set Γ) := Subgroup.le_normalizer ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp htn x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp hkn x).mp hx.2⟩
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp htn x).mpr hx.1,
        (Subgroup.mem_normalizer_iff.mp hkn x).mpr hx.2⟩
  have hLC : ¬ L ≤ cStarIn G T := by
    intro hle
    apply S.ne
    refine le_antisymm (cStarIn_le G T) ?_
    exact (sym_frattini S).trans (sup_le (sym_ker_le_cStarIn S) hle)
  have hLtop : imgG G φ L = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨g, hgσ⟩ := S.data.φ_surj σ
    have hg : (g : Γ) ∈ kerG G φ ⊔ L := sym_frattini S g.2
    have hmul : ((L ⊔ kerG G φ : Subgroup Γ) : Set Γ) = (L : Set Γ) * (kerG G φ : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right L (kerG G φ)
        (hLG.trans (le_normalizer_kerG G φ))
    rw [sup_comm, ← SetLike.mem_coe, hmul] at hg
    obtain ⟨l, hl, r, hr, hlr⟩ := hg
    obtain ⟨hrG, hr1⟩ := mem_kerG.1 hr
    refine mem_imgG.2 ⟨l, hLG hl, hl, ?_⟩
    have hgl : (g : Γ) = l * r := hlr.symm
    have e : g = ⟨l, hLG hl⟩ * ⟨r, hrG⟩ := Subtype.ext hgl
    rw [← hgσ, e, map_mul, hr1, mul_one]
  by_contra hne
  have hLlt : L < G := by
    refine lt_of_le_of_ne hLG fun heq => hne ?_
    intro g hg
    have : g ∈ L := by
      rw [heq]
      exact hg
    exact this.2
  exact hno L ⟨hLlt, (inf_le_left : baum T ≤ T).trans hTL, hLC⟩ hLtop

end CFSG.CGT.PushingUpLit.SYMB
