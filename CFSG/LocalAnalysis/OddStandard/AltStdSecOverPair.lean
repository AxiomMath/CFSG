module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecOverDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdSecWreathConfig

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdSec.Wreath

section Basic

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G} {H : Subgroup G}

theorem WreathPair.comm' (hH : WreathPair L z n H) {a b : G} (ha : a ∈ H) (hb : b ∈ cjSub z H) :
    a * b = b * a :=
  hH.comm a ha b hb

theorem WreathPair.eq_one_of_mem_inf (hH : WreathPair L z n H) (hn : 4 ≤ n) {a : G} (ha : a ∈ H)
    (ha' : a ∈ cjSub z H) : a = 1 := by
  obtain ⟨e⟩ := hH.iso
  have hz : (⟨a, ha⟩ : H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hH.comm' g.2 ha')
  rw [center_eq_bot_of_alt hn e, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem WreathPair.cjSub_ne (hH : WreathPair L z n H) (hn : 4 ≤ n) : cjSub z H ≠ H := by
  intro h
  obtain ⟨e⟩ := hH.iso
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_alt hn e
  apply hab
  exact Subtype.ext (hH.comm' a.2 (by rw [h]; exact b.2))

theorem WreathPair.ne_cjSub (hH : WreathPair L z n H) (hn : 4 ≤ n) : H ≠ cjSub z H :=
  (hH.cjSub_ne hn).symm

end Basic

section Conjugate

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {z : G} {H : Subgroup G}

theorem WreathPair.conjugate (hH : WreathPair L z n H) (g : G) :
    WreathPair (CFSG.conjugate L g) (g⁻¹ * z * g) n (CFSG.conjugate H g) where
  iso := ⟨(Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).symm.trans hH.iso.some⟩
  comm := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₁, ⟨b₀, hb₀, rfl⟩, rfl⟩ := hb
    have h1 := hH.comm a₀ ha₀ (z * b₀ * z⁻¹) ⟨b₀, hb₀, by simp [MulAut.conj_apply]⟩
    have e1 : (MulAut.conj g⁻¹).toMonoidHom a₀ *
        (MulAut.conj (g⁻¹ * z * g)).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom b₀) =
        g⁻¹ * (a₀ * (z * b₀ * z⁻¹)) * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj (g⁻¹ * z * g)).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom b₀) *
        (MulAut.conj g⁻¹).toMonoidHom a₀ = g⁻¹ * ((z * b₀ * z⁻¹) * a₀) * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, e2, h1]
  diag := by
    ext x
    have hd := Set.ext_iff.1 hH.diag
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨a₀, ha₀, hla⟩ := (hd l).1 hl
      refine ⟨(MulAut.conj g⁻¹).toMonoidHom a₀, ⟨a₀, ha₀, rfl⟩, ?_⟩
      have : (MulAut.conj g⁻¹).toMonoidHom l = (MulAut.conj g⁻¹).toMonoidHom
          (a₀ * (z * a₀ * z⁻¹)) := by rw [← hla]
      rw [this]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨a, ⟨a₀, ha₀, rfl⟩, rfl⟩
      refine ⟨a₀ * (z * a₀ * z⁻¹), (hd _).2 ⟨a₀, ha₀, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem WreathPair.wconfig (hH : WreathPair L z n H) (hn : 4 ≤ n) (hz2 : z * z = 1) :
    WConfig H z where
  sq := hz2
  comm a ha b hb := hH.comm a ha (z * b * z⁻¹) ⟨b, hb, by simp [MulAut.conj_apply]⟩
  inf a ha b hb hab := hH.eq_one_of_mem_inf hn ha (hab ▸ mem_cjSub_of_mem hb)

end Conjugate

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G} {H : Subgroup G}

theorem wreathPair_of_swap {L' : Subgroup G} (hH : WreathPair L z n H) (hn : 5 ≤ n) {w : G}
    (hw2 : w * w = 1) (hwH : cjSub w H = cjSub z H)
    (hcomm : ⁅centralizer ({w} : Set G), centralizer ({w} : Set G)⁆ ≤ L')
    (hcard : Nat.card L' ≤ Nat.card H) : WreathPair L' w n H := by
  obtain ⟨e⟩ := hH.iso
  have hmem : ∀ b ∈ H, w * b * w⁻¹ ∈ cjSub z H := fun b hb => by
    have := mem_cjSub_of_mem (g := w) hb
    rwa [hwH] at this
  have hc : WConfig H w :=
    { sq := hw2
      comm := fun a ha b hb => hH.comm a ha (w * b * w⁻¹) (hmem b hb)
      inf := fun a ha b hb hab =>
        hH.eq_one_of_mem_inf (by omega) ha (hab ▸ hmem b hb) }
  let θ : ↥H →* G := MonoidHom.mk' (fun a => Phi w (a : G) (a : G)) (fun a b => by
    have := hc.Phi_mul (a := (a : G)) (b := (a : G)) (a' := (b : G)) (b' := (b : G)) b.2 a.2
    simp only [Subgroup.coe_mul]
    exact this.symm)
  have hθ : ∀ a : ↥H, θ a = Phi w (a : G) (a : G) := fun a => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact Subtype.ext (hc.Phi_inj a.2 a.2 b.2 b.2 hab).1
  have hperf : Group.IsPerfect ↥H := ⟨(isQuasisimple_of_alt (by omega) e).1⟩
  have hDperf : Group.IsPerfect θ.range := Group.IsPerfect.range θ
  have hD : θ.range = ⁅θ.range, θ.range⁆ := (Subgroup.isPerfect_iff.mp hDperf).symm
  have hDC : θ.range ≤ centralizer ({w} : Set G) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff, hθ]
    have h1 := hc.z_Phi a.2 a.2
    calc Phi w (a : G) (a : G) * w = (w * Phi w (a : G) (a : G) * w⁻¹) * w := by rw [h1]
      _ = w * Phi w (a : G) (a : G) := by group
  have hDL : θ.range ≤ L' :=
    calc θ.range = ⁅θ.range, θ.range⁆ := hD
      _ ≤ ⁅centralizer ({w} : Set G), centralizer ({w} : Set G)⁆ :=
        Subgroup.commutator_mono hDC hDC
      _ ≤ L' := hcomm
  have hcardD : Nat.card θ.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm
  have hDeq : θ.range = L' := Subgroup.eq_of_le_of_card_ge hDL (by rw [hcardD]; exact hcard)
  refine ⟨⟨e⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have := hc.comm a ha b₀ hb₀
    simpa [MulAut.conj_apply] using this
  · ext x
    rw [← hDeq]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩

end Swap

end CFSG.OddStandard.AltStdSec
