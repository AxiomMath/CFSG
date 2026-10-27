module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3O
public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbitC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.Blueprint
open scoped commutatorElement

namespace E3S3O

variable {Y : Type} [Group Y] [Finite Y]

noncomputable abbrev orbW (Rd : Subgroup Y) (a : Y) :
    Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) a) :=
  secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) a

noncomputable abbrev famW (Rd : Subgroup Y) (a : Y) : Set (Subgroup ↥(orbW Rd a)) :=
  restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) a) (orbW Rd a)

noncomputable abbrev imgW (Rd : Subgroup Y) (a : Y) (M : Subgroup Y) : Subgroup ↥(orbW Rd a) :=
  (secImg (CoreAssembly.conjClass (tightCore Rd)) a M).subgroupOf (orbW Rd a)

noncomputable abbrev imgD (Rd L : Subgroup Y) (a : Y) :
    Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) a) :=
  ⨆ M ∈ {M | M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) L ∧
    XMem (CoreAssembly.conjClass (tightCore Rd)) a M},
    secImg (CoreAssembly.conjClass (tightCore Rd)) a M

noncomputable abbrev sig (Rd : Subgroup Y) {a s : Y} (hs : s ∈ Subgroup.centralizer ({a} : Set Y))
    (hW : (orbW Rd a).map (secAct (conjInvariant_conjClass (tightCore Rd)) hs).toMonoidHom =
      orbW Rd a) : MulAut ↥(orbW Rd a) :=
  actW (conjInvariant_conjClass (tightCore Rd)) hs hW

section Cit3


structure Ctx (n : ℕ) (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y) (u : Y)
    (L Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y) : Prop where
  frame : E3Frame n R S t J u
  edge : TightEdgeless (secR R u)
  pi : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)
  star : L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  notNbr : L ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  cent : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
    ⁅u * t, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)
  core : tightCore Rd = J
  std : TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t
  orbit : omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
    orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)
  conj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (tightCore R) (u * t)
  notO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t) u
  thm4 : Thm4RBelow 3 n

@[expose] def StepW (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W →
      ∃ k k' : ↥(orbW Rd (u * t)), TwinBase3 (famW Rd (u * t)) (imgW Rd (u * t) (tightCore Rd))
          (imgW Rd (u * t) (tightCore R)) k k' ∧
        (SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t) →
          ∃ (N : Subgroup ↥(orbW Rd (u * t))) (_ : N.Normal), N = Subgroup.zpowers (k * k') ∧
            CentOmega3 (↥(orbW Rd (u * t)) ⧸ N))

@[expose] def StepA (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W →
      ∃ s : Y, IsUniqueInvolution L s ∧ ∃ hs : s ∈ Subgroup.centralizer ({u * t} : Set Y),
        ∃ hW : (orbW Rd (u * t)).map
            (secAct (conjInvariant_conjClass (tightCore Rd)) hs).toMonoidHom = orbW Rd (u * t),
          (∀ M ∈ famW Rd (u * t), M.map (sig Rd hs hW).toMonoidHom ∈ famW Rd (u * t)) ∧
            sig Rd hs hW * sig Rd hs hW = 1 ∧
            ∀ x ∈ imgW Rd (u * t) (tightCore Rd), sig Rd hs hW x = x

@[expose] def StepB (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W → ∀ s : Y, IsUniqueInvolution L s →
      ∀ (hs : s ∈ Subgroup.centralizer ({u * t} : Set Y))
        (hW : (orbW Rd (u * t)).map
          (secAct (conjInvariant_conjClass (tightCore Rd)) hs).toMonoidHom = orbW Rd (u * t)),
        ∃ Q : Subgroup ↥(orbW Rd (u * t)), IsSylow2In Q (imgW Rd (u * t) (tightCore R)) ∧
          ∃ w ∈ Q, orderOf w = 4 ∧ ∀ x ∈ Q, sig Rd hs hW x = w * x * w⁻¹

@[expose] def StepC (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W → ∀ s : Y, IsUniqueInvolution L s →
      ∀ (hs : s ∈ Subgroup.centralizer ({u * t} : Set Y))
        (hW : (orbW Rd (u * t)).map
          (secAct (conjInvariant_conjClass (tightCore Rd)) hs).toMonoidHom = orbW Rd (u * t)),
        imgD Rd L (u * t) ≤ orbW Rd (u * t) ∧
          sigmaFixGen (imgW Rd (u * t) (tightCore Rd)) (sig Rd hs hW) =
            (imgD Rd L (u * t)).subgroupOf (orbW Rd (u * t))

@[expose] def StepD (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W → ∀ s : Y, IsUniqueInvolution L s →
      ∀ (hs : s ∈ Subgroup.centralizer ({u * t} : Set Y))
        (hW : (orbW Rd (u * t)).map
          (secAct (conjInvariant_conjClass (tightCore Rd)) hs).toMonoidHom = orbW Rd (u * t)),
        ∀ M ∈ CoreAssembly.conjClass (imgW Rd (u * t) (tightCore Rd)),
          (∀ x ∈ M, sig Rd hs hW x = x) →
            M ∉ omegaNbr (famW Rd (u * t)) (imgW Rd (u * t) (tightCore Rd))

@[expose] def StepE (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {J : Subgroup Y}
    {u : Y} {L Rd : Subgroup Y} {Sd : Sylow 2 Rd} {S' : Sylow 2 Y} {R' T W : Subgroup Y},
    Ctx n R S t J u L Rd Sd S' R' T W →
      (LieModel ↥(imgD Rd L (u * t)) .PSU 3 3 1 ∨ LieModel ↥(imgD Rd L (u * t)) .PSL 3 3 1) →
        LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSL 3 3 1 ∨
          LieModel (E3.OrbQ (CoreAssembly.conjClass (tightCore R)) J (tightCore R)) .PSU 3 3 1

theorem tightE3S3OConfig_of_steps {n : ℕ} (hSW : StepW n) (hSA : StepA n) (hSB : StepB n)
    (hSC : StepC n) (hSD : StepD n) (hSE : StepE n) (h4 : Thm4RBelow 3 n)
    (hOrb : TightE3S3Orbit n) : TightE3S3OConfig n := by
  intro Y _ _ R S t J u hF htu ht hedge hμ hO2 h163 L hLπ hLs hLn hc Rd Sd S' R' T W hcore hs
  obtain ⟨hconj, hnO2⟩ :=
    hOrb Y R S t J u hF htu ht hedge hμ hO2 L hLπ hLs hLn hc Rd Sd S' R' T W hcore hs
  have hctx : Ctx n R S t J u L Rd Sd S' R' T W :=
    { frame := hF, edge := hedge, pi := hLπ, star := hLs, notNbr := hLn, cent := hc,
      core := hcore, std := hs, orbit := hF.omegaNbr_subset_orbOf htu ht h163, conj := hconj,
      notO2 := hnO2, thm4 := h4 }
  obtain ⟨k, k', hbase, hN⟩ := hSW hctx
  obtain ⟨s, hsL, hsa, hW, hperm, hsq, hfix⟩ := hSA hctx
  have hC := hSC hctx s hsL hsa hW
  refine ⟨famW Rd (u * t), imgW Rd (u * t) (tightCore Rd), imgW Rd (u * t) (tightCore R), k, k',
    sig Rd hsa hW, ⟨hbase, hperm, hsq, hfix, hSB hctx s hsL hsa hW, hSD hctx s hsL hsa hW⟩, hN,
    fun hY => hSE hctx ?_⟩
  rw [hC.2] at hY
  have e : ↥((imgD Rd L (u * t)).subgroupOf (orbW Rd (u * t))) ≃* ↥(imgD Rd L (u * t)) :=
    Subgroup.subgroupOfEquivOfLe hC.1
  rcases hY with h | h
  · exact Or.inl (lieModel_congr e (Or.inr rfl) h)
  · exact Or.inr (lieModel_congr e (Or.inl rfl) h)

end Cit3

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
