module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWLab
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPhi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAut2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

section PhiM

variable {M : Type*} [Group M] {D E : Subgroup M} {eD : D ≃* DihedralGroup 4} {t : M}
  {eltE : ℕ → M}

theorem hltC : ∀ a b : ℕ, a < 128 → b < 128 → mulC a b < 128 := fun _ _ ha hb => mulC_lt ha hb

namespace DECtx

variable (hctx : DECtx D E eD t eltE) [hW : (D ⊔ E).Normal]

include hctx

@[expose] noncomputable def PhiAut : M →* ↥AutC :=
  (phiEquiv hctx.tabLab hltC).toMonoidHom.comp MulAut.conjNormal

@[expose] noncomputable def Phi : M →* ↥Pg :=
  (MulEquiv.subgroupCongr pg_eq_autC.symm).toMonoidHom.comp hctx.PhiAut

theorem Phi_coe (m : M) :
    ((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) = toPerm hctx.tabLab (MulAut.conjNormal m) := rfl

theorem Phi_lab (m : M) (i : Fin 128) :
    labD eD eltE (((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) i : ℕ) =
      m * labD eD eltE i * m⁻¹ := by
  have h := congrArg Subtype.val (toPerm_apply hctx.tabLab (MulAut.conjNormal m) i)
  rw [MulAut.conjNormal_apply] at h
  rw [Phi_coe]
  exact h

theorem lab_inj {a b : ℕ} (ha : a < 128) (hb : b < 128)
    (h : labD eD eltE a = labD eD eltE b) : a = b :=
  hctx.tabLab.inj a ha b hb h

theorem Phi_eq_of_perm (m : M) (G : Equiv.Perm (Fin 128))
    (h : ∀ i : Fin 128, m * labD eD eltE i * m⁻¹ = labD eD eltE (G i : ℕ)) :
    ((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) = G := by
  refine Equiv.ext fun i => Fin.ext ?_
  apply hctx.lab_inj (Fin.is_lt _) (Fin.is_lt _)
  rw [hctx.Phi_lab, h]

theorem Phi_eq_of_table (m : M) (r : Array ℕ) {G : Equiv.Perm (Fin 128)} (hG : Rep 128 r G)
    (h : ∀ c < 128, m * labD eD eltE c * m⁻¹ = labD eD eltE r[c]!) :
    ((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) = G :=
  hctx.Phi_eq_of_perm m G fun i => by rw [h i i.2, hG i]

theorem Phi_eq_one_iff (m : M) : hctx.Phi m = 1 ↔ ∀ w ∈ D ⊔ E, m * w = w * m := by
  constructor
  · intro h1 w hw
    obtain ⟨c, hc, rfl⟩ := hctx.tabLab.surj w hw
    have h2 := hctx.Phi_lab m ⟨c, hc⟩
    have h3 : ((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) = 1 := by rw [h1]; rfl
    rw [h3] at h2
    simp only [Equiv.Perm.one_apply] at h2
    have h4 : m * labD eD eltE c * m⁻¹ = labD eD eltE c := h2.symm
    calc m * labD eD eltE c = m * labD eD eltE c * m⁻¹ * m := by group
      _ = labD eD eltE c * m := by rw [h4]
  · intro h
    apply Subtype.ext
    refine Equiv.ext fun i => Fin.ext ?_
    apply hctx.lab_inj (Fin.is_lt _) (Fin.is_lt _)
    rw [hctx.Phi_lab]
    have h5 := h _ (hctx.lab_mem i i.2)
    show _ = labD eD eltE (((1 : Equiv.Perm (Fin 128)) i : Fin 128) : ℕ)
    rw [Equiv.Perm.one_apply, h5]
    group

theorem Phi_ker : hctx.Phi.ker = Subgroup.centralizer ((D ⊔ E : Subgroup M) : Set M) := by
  ext m
  rw [MonoidHom.mem_ker, hctx.Phi_eq_one_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    exact (h w hw).symm
  · intro h w hw
    exact (h w hw).symm

theorem Phi_t (m : M) : m * t * m⁻¹ = t := by
  have hF : ((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) ∈ AutC := pg_le_autC (hctx.Phi m).2
  have h1 := permVal_tC hF
  rw [permVal_eq _ tC_lt] at h1
  have h2 := hctx.Phi_lab m ⟨tC, tC_lt⟩
  have h3 : labD eD eltE (((hctx.Phi m : ↥Pg) : Equiv.Perm (Fin 128)) ⟨tC, tC_lt⟩ : ℕ) =
      labD eD eltE tC := by rw [h1]
  rw [h3, hctx.lab_tC] at h2
  exact h2.symm

theorem t_central (m : M) : m * t = t * m := by
  have := hctx.Phi_t m
  calc m * t = m * t * m⁻¹ * m := by group
    _ = t * m := by rw [this]

theorem Phi_surj (hsurj : ∀ α : MulAut ↥(D ⊔ E), ∃ m : M, MulAut.conjNormal m = α) :
    Function.Surjective hctx.Phi := by
  intro g
  have hg : (g : Equiv.Perm (Fin 128)) ∈ AutC := pg_le_autC g.2
  obtain ⟨m, hm⟩ := hsurj (ofPerm hctx.tabLab hltC g hg)
  refine ⟨m, Subtype.ext ?_⟩
  rw [Phi_coe, hm]
  exact toPerm_ofPerm hctx.tabLab hltC g hg

end DECtx

end PhiM

end CFSG.EvenSporadicStandard.Fin76b.W16
