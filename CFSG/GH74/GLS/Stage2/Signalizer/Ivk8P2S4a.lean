module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aFit
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
import CFSG.GH74.GLS.Stage2.Bender.Thm2.Proofs11
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Local.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4a

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_of_commutator_eq {z : G} {X M : Subgroup G} (hz2 : z * z = 1)
    (hMz : M = centralizer ({z} : Set G)) (hzX : z ∈ normalizer (X : Set G))
    (hF1 : Fpi (piF' M) X ⊓ M = ⊥) (hF2 : Fpi (piF M) X ≤ M)
    (ha : ⁅X, zpowers z⁆ ≤ Em X ⊔ (X ⊓ centralizer (Em X : Set G)))
    (hXz : ⁅X, zpowers z⁆ = X) : X = Em X ⊔ Fpi (piF' M) X := by
  have hzE : z ∈ normalizer ((Em X : Subgroup G) : Set G) := mem_normalizer_Em hzX
  have hzF1 : z ∈ normalizer ((Fpi (piF' M) X : Subgroup G) : Set G) :=
    mem_normalizer_Fpi _ hzX
  have hXE : X ≤ normalizer ((Em X : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_Em (Subgroup.le_normalizer hx)
  have hXF1 : X ≤ normalizer ((Fpi (piF' M) X : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_Fpi _ (Subgroup.le_normalizer hx)
  have hXF2 : X ≤ normalizer ((Fpi (piF M) X : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_Fpi _ (Subgroup.le_normalizer hx)
  have hXFs : X ≤ normalizer ((Fs X : Subgroup G) : Set G) := le_normalizer_Fs X
  have hF1X : Fpi (piF' M) X ≤ X := (Fpi_le_Fm _ X).trans (Fm_le X)
  have hF2X : Fpi (piF M) X ≤ X := (Fpi_le_Fm _ X).trans (Fm_le X)
  have hEX : Em X ≤ X := Em_le X
  have hFm : Fm X ≤ Fpi (piF M) X ⊔ Fpi (piF' M) X :=
    Fm_le_Fpi_sup (fun r => r ∣ Nat.card ↥(Fm M)) X
  have hzF2 : ∀ f ∈ Fpi (piF M) X, z * f = f * z := fun f hf => by
    have : f ∈ centralizer ({z} : Set G) := hMz ▸ hF2 hf
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hfpf : ∀ f ∈ Fpi (piF' M) X, z * f = f * z → f = 1 := fun f hf hc => by
    have hfz : f ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hc.symm
    exact Subgroup.mem_bot.1 (hF1 ▸ (⟨hf, hMz ▸ hfz⟩ : f ∈ Fpi (piF' M) X ⊓ M))
  have hinv : Inverts z (Fpi (piF' M) X) := inverts_of_fixed_free hz2 hzF1 hfpf
  have hcent2 : ∀ u ∈ X, ∀ f ∈ Fpi (piF M) X,
      (u * z * u⁻¹ * z⁻¹) * f = f * (u * z * u⁻¹ * z⁻¹) := by
    intro u hu f hf
    have hg : u⁻¹ * f * u ∈ Fpi (piF M) X := by
      have := (mem_normalizer_iff.mp (hXF2 (X.inv_mem hu)) f).mp hf
      simpa using this
    have hzf : z * f = f * z := hzF2 f hf
    have hzg : z * (u⁻¹ * f * u) = (u⁻¹ * f * u) * z := hzF2 _ hg
    have h1 : z⁻¹ * f * z = f := by
      calc z⁻¹ * f * z = z⁻¹ * (f * z) := by group
        _ = z⁻¹ * (z * f) := by rw [hzf]
        _ = f := by group
    have h2 : z * (u⁻¹ * f * u) * z⁻¹ = u⁻¹ * f * u := by
      calc z * (u⁻¹ * f * u) * z⁻¹ = ((u⁻¹ * f * u) * z) * z⁻¹ := by rw [hzg]
        _ = u⁻¹ * f * u := by group
    have h3 : (u * z * u⁻¹ * z⁻¹) * f * (u * z * u⁻¹ * z⁻¹)⁻¹ = f := by
      calc (u * z * u⁻¹ * z⁻¹) * f * (u * z * u⁻¹ * z⁻¹)⁻¹
          = u * z * u⁻¹ * (z⁻¹ * f * z) * u * z⁻¹ * u⁻¹ := by group
        _ = u * z * u⁻¹ * f * u * z⁻¹ * u⁻¹ := by rw [h1]
        _ = u * (z * (u⁻¹ * f * u) * z⁻¹) * u⁻¹ := by group
        _ = u * (u⁻¹ * f * u) * u⁻¹ := by rw [h2]
        _ = f := by group
    calc (u * z * u⁻¹ * z⁻¹) * f
        = (u * z * u⁻¹ * z⁻¹) * f * (u * z * u⁻¹ * z⁻¹)⁻¹ * (u * z * u⁻¹ * z⁻¹) := by group
      _ = f * (u * z * u⁻¹ * z⁻¹) := by rw [h3]
  have hFcent : ∀ u ∈ X, ∀ f ∈ Fm X, (u * z * u⁻¹ * z⁻¹) * f = f * (u * z * u⁻¹ * z⁻¹) := by
    intro u hu
    have hFle : Fm X ≤ centralizer ({u * z * u⁻¹ * z⁻¹} : Set G) := by
      refine hFm.trans (sup_le (fun f hf => ?_) (fun f hf => ?_))
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcent2 u hu f hf).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commutator_centralizes_of_inverts hz2 hinv (hXF1 hu) f hf).symm
    intro f hf
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hFle hf)).symm
  have hcommC0 : ∀ c ∈ X ⊓ centralizer ((Em X : Subgroup G) : Set G),
      c * z * c⁻¹ * z⁻¹ ∈ Fs X := by
    rintro c ⟨hcX, hcE⟩
    have hmemX : c * z * c⁻¹ * z⁻¹ ∈ X := by
      have h1 : z * c⁻¹ * z⁻¹ ∈ X := (mem_normalizer_iff.mp hzX c⁻¹).mp (X.inv_mem hcX)
      have := X.mul_mem hcX h1
      simpa [mul_assoc] using this
    have hcentE : ∀ e ∈ Em X, (c * z * c⁻¹ * z⁻¹) * e = e * (c * z * c⁻¹ * z⁻¹) := by
      intro e he
      have he' : z⁻¹ * e * z ∈ Em X := by
        have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hzE) e).mp he
        simpa using this
      have hce : ∀ w ∈ Em X, c * w = w * c := fun w hw =>
        (Subgroup.mem_centralizer_iff.mp hcE w hw).symm
      have hc1 : Commute c (z⁻¹ * e * z) := hce _ he'
      have hc2 : c * e = e * c := hce e he
      calc (c * z * c⁻¹ * z⁻¹) * e
          = c * z * (c⁻¹ * (z⁻¹ * e * z)) * z⁻¹ := by group
        _ = c * z * ((z⁻¹ * e * z) * c⁻¹) * z⁻¹ := by rw [hc1.inv_left.eq]
        _ = c * e * (z * c⁻¹ * z⁻¹) := by group
        _ = e * c * (z * c⁻¹ * z⁻¹) := by rw [hc2]
        _ = e * (c * z * c⁻¹ * z⁻¹) := by group
    have hFs : Fs X ≤ centralizer ({c * z * c⁻¹ * z⁻¹} : Set G) := by
      rw [Fs_eq_sup]
      refine sup_le (fun f hf => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hFcent c hcX f hf).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcentE e he).symm
    exact inf_centralizer_Fs_le X ⟨hmemX, Subgroup.mem_centralizer_iff.2 fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.1 (hFs hw)⟩
  have hcommE : ∀ e ∈ Em X, e * z * e⁻¹ * z⁻¹ ∈ Em X := by
    intro e he
    have h1 : z * e⁻¹ * z⁻¹ ∈ Em X := (mem_normalizer_iff.mp hzE e⁻¹).mp ((Em X).inv_mem he)
    have := (Em X).mul_mem he h1
    simpa [mul_assoc] using this
  have hT : Em X ⊔ (X ⊓ centralizer ((Em X : Subgroup G) : Set G)) ≤
      commPre z X (Fs X) hXFs := by
    refine sup_le (fun e he => ⟨hEX he, Em_le_Fs X (hcommE e he)⟩)
      (fun c hc => ⟨hc.1, hcommC0 c hc⟩)
  have hall : ∀ x ∈ X, x * z * x⁻¹ * z⁻¹ ∈ Fs X := by
    intro x hx
    have hx' : x ∈ ⁅X, zpowers z⁆ := by rw [hXz]; exact hx
    exact (hT (ha hx')).2
  have hXle : X ≤ Fs X := by
    intro x hx
    have hx' : x ∈ ⁅X, zpowers z⁆ := by rw [hXz]; exact hx
    exact commutator_zpowers_le_of_forall hz2 hall hx'
  have hXEF1 : X ≤ normalizer ((Em X ⊔ Fpi (piF' M) X : Subgroup G) : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_sup _ _ ⟨hXE hx, hXF1 hx⟩
  have hT' : Fs X ≤ commPre z X (Em X ⊔ Fpi (piF' M) X) hXEF1 := by
    rw [Fs_eq_sup]
    refine sup_le (hFm.trans (sup_le (fun f hf => ⟨hF2X hf, ?_⟩) (fun f hf => ⟨hF1X hf, ?_⟩)))
      (fun e he => ⟨hEX he, Subgroup.mem_sup_left (hcommE e he)⟩)
    · have hzf : z * f = f * z := hzF2 f hf
      have : f * z * f⁻¹ * z⁻¹ = 1 := by
        calc f * z * f⁻¹ * z⁻¹ = (z * f) * f⁻¹ * z⁻¹ := by rw [hzf]
          _ = 1 := by group
      rw [this]
      exact Subgroup.one_mem _
    · have h1 : z * f⁻¹ * z⁻¹ = f⁻¹⁻¹ := hinv f⁻¹ ((Fpi (piF' M) X).inv_mem hf)
      have : f * z * f⁻¹ * z⁻¹ = f * f := by
        calc f * z * f⁻¹ * z⁻¹ = f * (z * f⁻¹ * z⁻¹) := by group
          _ = f * f := by rw [h1, inv_inv]
      rw [this]
      exact Subgroup.mem_sup_right ((Fpi (piF' M) X).mul_mem hf hf)
  refine le_antisymm ?_ (sup_le hEX hF1X)
  intro x hx
  have hx' : x ∈ ⁅X, zpowers z⁆ := by rw [hXz]; exact hx
  exact commutator_zpowers_le_of_forall hz2 (fun y hy => (hT' (hXle hy)).2) hx'

end Core

section Main

variable {G : Type} [Group G] [Finite G]

theorem z_mem_Vof {z : G} {M E : Subgroup G} {p : ℕ} (hMz : M = centralizer ({z} : Set G))
    (hz2 : orderOf z = 2) (hEM : E ≤ Op p M) : z ∈ Vof M E := by
  have hzM : z ∈ M := hMz ▸ Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hMc : M ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hmz : m * z = z * m :=
      Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ hm : m ∈ centralizer ({z} : Set G))
    have hc : Commute m z := hmz
    exact (hc.zpow_right n).eq.symm
  have hn : M ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    hMc.trans (Subgroup.centralizer_le_normalizer _)
  have hz2g : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hzOp : zpowers z ≤ Op 2 M :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.le_Op_of_normal (Subgroup.zpowers_le.2 hzM) hn hz2g
  have hzF : z ∈ Fm M := Op_le_Fm 2 Nat.prime_two M (hzOp (Subgroup.mem_zpowers z))
  refine ⟨hzF, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
  have heM : e ∈ M := Op_le p M (hEM he)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ heM : e ∈ centralizer ({z} : Set G))

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4a

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

theorem lemma18_5R_of (h171 : Prop17_1) (h184 : Lemma18_4ac) : Lemma18_5R := by
  intro G _ _ z k S M p E t hctx X hX
  obtain ⟨hXbot, hXtop, hXv, hXz, hF1, hF2⟩ := hX
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hMz : M = centralizer ({z} : Set G) := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hz2' : orderOf z = 2 := hS2.orderOf_z
  have hz2 : z * z = 1 := by
    have : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hz2')
    simpa [pow_two] using this
  have hzV : z ∈ Vof M E := P2S4a.z_mem_Vof hMz hz2' hctx.E_le
  have hzX : z ∈ normalizer (X : Set G) := hXv z hzV
  have hXM : ¬ X ≤ M := by
    intro hXM
    apply hXbot
    rw [← hXz]
    refine le_bot_iff.1 (P2S4a.commutator_zpowers_le_of_forall hz2 (fun x hx => ?_))
    have hxc : x ∈ centralizer ({z} : Set G) := hMz ▸ hXM hx
    have hc : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
    have : x * z * x⁻¹ * z⁻¹ = 1 := by rw [hc]; group
    exact Subgroup.mem_bot.2 this
  have ha : ⁅X, zpowers z⁆ ≤ Em X ⊔ (X ⊓ centralizer (Em X : Set G)) := by
    by_cases hJ : ∃ J, IsCompIn X J
    · obtain ⟨J, hJ⟩ := hJ
      exact (h184 G z k S M p E t hctx X hXv hXM hXtop J hJ).1.2
    · push Not at hJ
      have hE : Em X = ⊥ := P2S4a.Em_eq_bot_of_no_comp hJ
      refine le_sup_of_le_right (le_inf ?_ ?_)
      · refine P2S4a.commutator_zpowers_le_of_forall hz2 fun x hx => ?_
        have h1 : z * x⁻¹ * z⁻¹ ∈ X := (mem_normalizer_iff.mp hzX x⁻¹).mp (X.inv_mem hx)
        have := X.mul_mem hx h1
        simpa [mul_assoc] using this
      · intro y _
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hh' : h ∈ Em X := hh
        rw [hE, Subgroup.mem_bot] at hh'
        rw [hh', one_mul, mul_one]
  exact P2S4a.eq_sup_of_commutator_eq hz2 hMz hzX hF1 hF2 ha hXz

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
