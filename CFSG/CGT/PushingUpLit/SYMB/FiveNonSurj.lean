module

public import CFSG.CGT.PushingUpLit.SYMB.FiveBound
public import CFSG.CGT.PushingUpLit.SYMB.FiveF3
public import CFSG.CGT.PushingUpLit.SYMB.FiveSwap

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7 Equiv
open scoped commutatorElement

theorem gamma_facts : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    (swap a c * swap b d) * swap a b * (swap a c * swap b d)⁻¹ = swap c d ∧
    (swap a c * swap b d) * swap c d * (swap a c * swap b d)⁻¹ = swap a b ∧
    (swap a c * swap b d)⁻¹ * swap c d * (swap a c * swap b d) = swap a b ∧
    swap a b * (swap a c * swap b d)⁻¹ * (swap a b)⁻¹ * (swap a c * swap b d) =
      swap a b * swap c d := by
  set_option synthInstance.maxSize 2000 in decide +kernel

theorem conjSub_zpowers' {M : Type*} [Group M] (σ t : M) :
    B6.conjSub σ (Subgroup.zpowers t) = Subgroup.zpowers (σ * t * σ⁻¹) := by
  show (Subgroup.zpowers t).map (MulAut.conj σ).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  rfl

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {E : Subgroup Γ} {a b c d : Fin 5}

omit [Finite Γ] in
theorem exists_g (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hp : Pts G T φ a b c d) :
    ∃ g : Γ, ∃ hgE : g ∈ E, g ∈ T ∧ φ ⟨g, hc.join.le hgE⟩ = swap a c * swap b d := by
  have hγ : swap a c * swap b d ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hp.hac,
      Equiv.Perm.sign_swap hp.hbd]
    rfl
  have hγE : swap a c * swap b d ∈ imgG G φ E := by
    rw [hc.join.img_eq_alt]
    exact hγ
  obtain ⟨g, hgG, hgE, hgφ⟩ := mem_imgG.1 hγE
  refine ⟨g, hgE, ?_, hgφ⟩
  obtain ⟨t, htG, htT, htφ⟩ := mem_imgG.1
    (swap_mul_swap_mem_imgG S hker hp.hab hp.hcd hp.hac hp.had hp.hbc hp.hbd hp.hY)
  have h1 : t⁻¹ * g ∈ kerG G φ := by
    refine mem_kerG.2 ⟨G.mul_mem (G.inv_mem htG) hgG, ?_⟩
    show φ ((⟨t, htG⟩ : ↥G)⁻¹ * ⟨g, hgG⟩) = 1
    rw [map_mul, map_inv, htφ, hgφ, inv_mul_cancel]
  have h2 : g = t * (t⁻¹ * g) := by group
  rw [h2]
  exact T.mul_mem htT (hker h1)

theorem exists_avoid (hc : FiveCase S E) (hker : kerG G φ ≤ T) (hV : V1Iso S ⁅V, E⁆)
    (hp : Pts G T φ a b c d) {z : Γ} (hz2 : z * z = 1) (hzG : ∀ g ∈ G, g * z = z * g)
    (hzV : z ∉ ⁅V, E⁆)
    (hsq : ∀ (e : Γ) (he : e ∈ E), (φ ⟨e, hc.join.le he⟩) ^ 2 = 1 → φ ⟨e, hc.join.le he⟩ ≠ 1 →
      z⁻¹ * e ^ 2 ∈ ⁅V, E⁆)
    {x : Γ} (hxG : x ∈ G) (hx2 : x * x = 1) (hφx : φ ⟨x, hxG⟩ = swap a b)
    {A₀ : Subgroup Γ}
    (hA₀ : A₀ ∈ Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x) :
    ∃ A' ∈ Wset G T φ (Subgroup.zpowers (swap c d)),
      ∀ A ∈ Wx G T φ (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) x,
        Up φ ψ ⁅V, E⁆ A (Subgroup.zpowers (swap c d)) ≠ A' := by
  classical
  obtain ⟨g, hgE, hgT, hgφ⟩ := exists_g hc hker hp
  have hgG : g ∈ G := hc.join.le hgE
  obtain ⟨hγ1, hγ2, hγ3, hγ4⟩ :=
    gamma_facts a b c d hp.hab hp.hcd hp.hac hp.had hp.hbc hp.hbd
  have hA₁W : B6.conjSub g A₀ ∈ Wset G T φ
      (Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) := by
    refine ⟨isMax_conjSub hgT hA₀.1.1, ?_⟩
    rw [imgG_conjSub hgG, hA₀.1.2, hgφ, OrderIso.map_sup, conjSub_zpowers', conjSub_zpowers',
      hγ1, hγ2, sup_comm]
  refine ⟨Up φ ψ ⁅V, E⁆ (B6.conjSub g A₀) (Subgroup.zpowers (swap c d)),
    Up_mem_Wset hV hp hA₁W Good.Y Good.t₂ le_sup_right, ?_⟩
  intro A hA hEq
  have hAY : imgG G φ A = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d) := hA.1.2
  have ht2 : swap c d ∈ imgG G φ A := by
    rw [hAY]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨w, hwG, hwA, hwφ⟩ := mem_imgG.1 ht2
  have hwU : w ∈ Up φ ψ ⁅V, E⁆ A (Subgroup.zpowers (swap c d)) :=
    (show A ⊓ preimG G φ (Subgroup.zpowers (swap c d)) ≤
        Up φ ψ ⁅V, E⁆ A (Subgroup.zpowers (swap c d)) from le_sup_right)
      ⟨hwA, mem_preimG.2 ⟨hwG, by rw [hwφ]; exact Subgroup.mem_zpowers _⟩⟩
  rw [hEq] at hwU
  obtain ⟨cc, hcc, w', hw', hww'⟩ := exists_mem_Up hV hwU
  have hw'G : w' ∈ G := (mem_preimG.1 hw'.2).1
  have hccK : cc ∈ kerG G φ := Cfix_le_kerG hV _ hcc
  obtain ⟨hccG, hccφ⟩ := mem_kerG.1 hccK
  have hw'φ : φ ⟨w', hw'G⟩ = swap c d := by
    have h1 : φ ⟨w, hwG⟩ = φ ⟨cc, hccG⟩ * φ ⟨w', hw'G⟩ := by
      have : (⟨w, hwG⟩ : ↥G) = ⟨cc, hccG⟩ * ⟨w', hw'G⟩ := Subtype.ext hww'
      rw [this, map_mul]
    rw [hwφ, hccφ, one_mul] at h1
    exact h1.symm
  have ha'A₀ : g⁻¹ * w' * g ∈ A₀ := B6.mem_conjSub.1 hw'.1
  have ha'G : g⁻¹ * w' * g ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hgG) hw'G) hgG
  have ha'φ : φ ⟨g⁻¹ * w' * g, ha'G⟩ = swap a b := by
    have h1 : φ ⟨g⁻¹ * w' * g, ha'G⟩ =
        (φ ⟨g, hgG⟩)⁻¹ * φ ⟨w', hw'G⟩ * φ ⟨g, hgG⟩ := by
      show φ ((⟨g, hgG⟩ : ↥G)⁻¹ * ⟨w', hw'G⟩ * ⟨g, hgG⟩) = _
      rw [map_mul, map_mul, map_inv]
    rw [h1, hw'φ, hgφ, hγ3]
  have hxa' : x * (g⁻¹ * w' * g) = (g⁻¹ * w' * g) * x :=
    elemAb_comm hA₀.1.1.2.1 hA₀.2 ha'A₀
  have hc₀G : (g⁻¹ * w' * g) * x⁻¹ ∈ G := G.mul_mem ha'G (G.inv_mem hxG)
  have hc₀R : (g⁻¹ * w' * g) * x⁻¹ ∈ kerG G φ := by
    refine mem_kerG.2 ⟨hc₀G, ?_⟩
    show φ ((⟨g⁻¹ * w' * g, ha'G⟩ : ↥G) * (⟨x, hxG⟩ : ↥G)⁻¹) = 1
    rw [map_mul, map_inv, ha'φ, hφx, mul_inv_cancel]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hc₀x : ((g⁻¹ * w' * g) * x⁻¹) * x = (g⁻¹ * w' * g) := by group
  have hcx : ((g⁻¹ * w' * g) * x⁻¹) * x = x * ((g⁻¹ * w' * g) * x⁻¹) := by
    rw [hc₀x]
    calc g⁻¹ * w' * g = (x * (g⁻¹ * w' * g)) * x⁻¹ := by
          rw [hxa']; group
      _ = x * ((g⁻¹ * w' * g) * x⁻¹) := by group
  have hhE : x * g⁻¹ * x⁻¹ * g ∈ E := by
    have h1 : x * g⁻¹ * x⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hc.normal hxG) g⁻¹).mp (E.inv_mem hgE)
    exact E.mul_mem h1 hgE
  have hhφ : φ ⟨x * g⁻¹ * x⁻¹ * g, hc.join.le hhE⟩ = swap a b * swap c d := by
    have h1 : φ ⟨x * g⁻¹ * x⁻¹ * g, hc.join.le hhE⟩ =
        φ ⟨x, hxG⟩ * (φ ⟨g, hgG⟩)⁻¹ * (φ ⟨x, hxG⟩)⁻¹ * φ ⟨g, hgG⟩ := by
      show φ ((⟨x, hxG⟩ : ↥G) * (⟨g, hgG⟩ : ↥G)⁻¹ * (⟨x, hxG⟩ : ↥G)⁻¹ * ⟨g, hgG⟩) = _
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [h1, hφx, hgφ, hγ4]
  have hh2 : z⁻¹ * ((x * g⁻¹ * x⁻¹ * g) * (x * g⁻¹ * x⁻¹ * g)) ∈ ⁅V, E⁆ := by
    have := hsq _ hhE (by rw [hhφ, pow_two]; exact swap_pair_sq hp.hac hp.had hp.hbc hp.hbd)
      (by rw [hhφ]; exact swap_mul_swap_ne_one hp.hab hp.hac hp.had)
    rwa [pow_two] at this
  have hF3 := comm_conj_mem hc hz2 hzG hxG hc₀R hgE hx2 hcx hh2
  rw [hc₀x] at hF3
  have hw'eq : g * (g⁻¹ * w' * g) * g⁻¹ = w' := by group
  rw [hw'eq] at hF3
  have hwA' : cc * w' ∈ A := by rw [← hww']; exact hwA
  have hxw : x * (cc * w') = (cc * w') * x := elemAb_comm hA.1.1.2.1 hA.2 hwA'
  have hcc1 : cc ∈ ⁅V, E⁆ := Cfix_le _ hcc
  have hxcc : x * cc⁻¹ * x⁻¹ ∈ ⁅V, E⁆ :=
    (Subgroup.mem_normalizer_iff.mp (hV.normal hxG) cc⁻¹).mp ((⁅V, E⁆).inv_mem hcc1)
  have hcomm : ⁅x, w'⁆ ∈ ⁅V, E⁆ := by
    have e1 : x * (cc * w') * x⁻¹ = cc * w' := by
      calc x * (cc * w') * x⁻¹ = ((cc * w') * x) * x⁻¹ := by rw [hxw]
        _ = cc * w' := by group
    have e2 : ⁅x, w'⁆ = (x * cc⁻¹ * x⁻¹) * cc := by
      simp only [commutatorElement_def]
      calc x * w' * x⁻¹ * w'⁻¹
          = (x * cc⁻¹ * x⁻¹) * (x * (cc * w') * x⁻¹) * (cc * w')⁻¹ * cc := by group
        _ = (x * cc⁻¹ * x⁻¹) * (cc * w') * (cc * w')⁻¹ * cc := by rw [e1]
        _ = (x * cc⁻¹ * x⁻¹) * cc := by group
    rw [e2]
    exact (⁅V, E⁆).mul_mem hxcc hcc1
  apply hzV
  have h1 : z⁻¹ ∈ ⁅V, E⁆ := by
    have e : z⁻¹ = (z⁻¹ * ⁅x, w'⁆) * (⁅x, w'⁆)⁻¹ := by group
    rw [e]
    exact (⁅V, E⁆).mul_mem hF3 ((⁅V, E⁆).inv_mem hcomm)
  have := (⁅V, E⁆).inv_mem h1
  rwa [inv_inv] at this

end CFSG.CGT.PushingUpLit.SYMB
