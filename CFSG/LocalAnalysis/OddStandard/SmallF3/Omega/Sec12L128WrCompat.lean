module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sec128_iota_eq_base {G : Type} [Group G] {V D : Subgroup G}
    {φ₀ : (Fin 5 → ZMod 2) → G}
    {ι : ↥V →* WrZ2 ↥D} {φ : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) → ↥V}
    (hι : ∀ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2), IsEvenVec w →
      (ι (φ q w)).right = 1 ∧
        ∀ q', ((ι (φ q w)).left q' : G) = if q' = q then φ₀ w else 1)
    (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2) (hw : IsEvenVec w) :
    ι (φ q w) = sec128WrBase (fun y => (ι (φ q w)).left y) := by
  ext y <;> simp [sec128WrBase, (hι q w hw).1]

theorem sec128_compat {G : Type} [Group G] {V D : Subgroup G} {φ₀ : (Fin 5 → ZMod 2) → G}
    {χ : ↥(alternatingGroup (Fin 5)) →* ↥D}
    (hχ : ∀ (a : ↥(alternatingGroup (Fin 5))) (v : Fin 5 → ZMod 2), IsEvenVec v →
      (χ a : G) * φ₀ v * (χ a : G)⁻¹ = φ₀ (permVec (a : Equiv.Perm (Fin 5)) v))
    {φ : Multiplicative (ZMod 2) → (Fin 5 → ZMod 2) → ↥V}
    (hgen : Subgroup.closure {x : ↥V | ∃ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2),
      IsEvenVec w ∧ φ q w = x} = ⊤)
    {ι : ↥V →* WrZ2 ↥D}
    (hι : ∀ (q : Multiplicative (ZMod 2)) (w : Fin 5 → ZMod 2), IsEvenVec w →
      (ι (φ q w)).right = 1 ∧
        ∀ q', ((ι (φ q w)).left q' : G) = if q' = q then φ₀ w else 1)
    {Y : Subgroup (MulAut ↥V)} (e : WrZ2 ↥(alternatingGroup (Fin 5)) ≃* ↥Y)
    (hact : ∀ (w : WrZ2 ↥(alternatingGroup (Fin 5))) (q : Multiplicative (ZMod 2))
      (v : Fin 5 → ZMod 2), IsEvenVec v →
        ((e w : ↥Y) : MulAut ↥V) (φ q v) =
          φ (w.right * q)
            (permVec ((w.left (w.right * q) : ↥(alternatingGroup (Fin 5))) :
              Equiv.Perm (Fin 5)) v)) :
    ∀ (γ : WrZ2 ↥(alternatingGroup (Fin 5))) (v : ↥V),
      ι (((e γ : ↥Y) : MulAut ↥V) v) = sec128WrMap χ γ * ι v * (sec128WrMap χ γ)⁻¹ := by
  intro γ v
  let s := γ.right
  let f : Multiplicative (ZMod 2) → ↥(alternatingGroup (Fin 5)) := γ.left
  let x : WrZ2 ↥D := sec128WrMap χ γ
  let F : ↥V →* WrZ2 ↥D := ((MulAut.conj x).toMonoidHom).comp ι
  let F' : ↥V →* WrZ2 ↥D := ι.comp ((e γ : ↥Y) : MulAut ↥V).toMonoidHom
  have hFF' : F = F' := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro v hv
    rcases hv with ⟨q, w, hw, rfl⟩
    let u : Fin 5 → ZMod 2 := permVec (f (s * q) : Equiv.Perm (Fin 5)) w
    have hu : IsEvenVec u := isEvenVec_permVec _ hw
    have hbase : ι (φ q w) = sec128WrBase (fun y => (ι (φ q w)).left y) :=
      sec128_iota_eq_base hι q w hw
    have hbaseu : ι (φ (s * q) u) = sec128WrBase (fun y => (ι (φ (s * q) u)).left y) :=
      sec128_iota_eq_base hι (s * q) u hu
    have hx : x = (⟨fun y => χ (f y), s⟩ : WrZ2 ↥D) := rfl
    calc
      F (φ q w) = x * ι (φ q w) * x⁻¹ := rfl
      _ = (⟨fun y => χ (f y), s⟩ : WrZ2 ↥D) *
            sec128WrBase (fun y => (ι (φ q w)).left y) *
            (⟨fun y => χ (f y), s⟩ : WrZ2 ↥D)⁻¹ := by
            conv_lhs => rw [hx, hbase]
      _ = sec128WrBase
            (fun y => χ (f y) * (ι (φ q w)).left (s⁻¹ * y) * (χ (f y))⁻¹) :=
            sec128Wr_conj_base (fun y => χ (f y)) s (fun y => (ι (φ q w)).left y)
      _ = sec128WrBase (fun y => (ι (φ (s * q) u)).left y) := by
            congr 1
            funext y
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [(hι q w hw).2 (s⁻¹ * y), (hι (s * q) u hu).2 y]
            by_cases hy : y = s * q
            · subst hy
              have hq : s⁻¹ * (s * q) = q := inv_mul_cancel_left s q
              simp only [hq, if_pos rfl]
              exact hχ (f (s * q)) w hw
            · have hs : s⁻¹ * y ≠ q := fun h => hy ((inv_mul_eq_iff_eq_mul).mp h)
              simp only [hs, hy]
              simp
      _ = ι (φ (s * q) u) := hbaseu.symm
      _ = ι (((e γ : ↥Y) : MulAut ↥V) (φ q w)) :=
            congrArg ι (hact γ q w hw).symm
      _ = F' (φ q w) := rfl
  change F' v = F v
  rw [hFF']

end CFSG.OddStandard.SmallF3.Omega
