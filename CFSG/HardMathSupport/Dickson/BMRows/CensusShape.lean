module

public import CFSG.HardMathSupport.Dickson.BMRows.Defs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271

theorem catalogIs_of_mulEquiv {P : TauCeti.CFSGIndex → Prop} (T T' : Type) [Group T] [Group T']
    (e : T ≃* T') (h : catalogIs T P) : catalogIs T' P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem pCompCensus_of_centShapeRk' {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    {P : TauCeti.CFSGIndex → Prop} {Rk : ∀ (T : Type) [Group T], Prop}
    (h : CentShapeRk' p (fun T _ => catalogIs T P) Rk Q) : PCompCensus p Q P := by
  intro x hx J hJ
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  rcases h x hx1 hxp with hno | ⟨J₀, -, hu, hg, -⟩
  · exact absurd hJ (hno J)
  · rw [hu J hJ]
    exact hg

end CFSG.HardMathSupport.Dickson.BMRows
