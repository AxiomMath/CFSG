module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public import CFSG.GH74.GLS.C3.Layer2.LocalBasic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem exists_aut_of_rel (Rel : Amb 5 → Amb 5 → Prop)
    (hdom : ∀ p r, Rel p r → p ∈ T5 ∧ r ∈ T5)
    (R1 : ∀ p ∈ T5, ∃ r, Rel p r)
    (R2 : ∀ p r r', Rel p r → Rel p r' → r = r')
    (R3 : ∀ p q r r', Rel p r → Rel q r' → Rel (p * q) (r * r'))
    (R4 : ∀ p q r, Rel p r → Rel q r → p = q)
    (R5 : ∀ r ∈ T5, ∃ p, Rel p r) :
    ∃ b : Amb 5 → Amb 5, IsAutOn b ∧ ∀ p ∈ T5, Rel p (b p) := by
  have hex : ∀ p : Amb 5, ∃ r : Amb 5, p ∈ T5 → Rel p r := by
    intro p
    by_cases hp : p ∈ T5
    · obtain ⟨r, hr⟩ := R1 p hp
      exact ⟨r, fun _ => hr⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose b hb using hex
  refine ⟨b, ⟨?_, ?_, ?_, ?_⟩, hb⟩
  · intro p hp
    exact (hdom _ _ (hb p hp)).2
  · intro p hp q hq
    exact R2 _ _ _ (hb _ (mul_mem hp hq)) (R3 _ _ _ _ (hb p hp) (hb q hq))
  · intro p hp q hq h
    exact R4 _ _ (b p) (hb p hp) (h ▸ hb q hq)
  · intro r hr
    obtain ⟨p, hp⟩ := R5 r hr
    have hpT : p ∈ T5 := (hdom _ _ hp).1
    exact ⟨p, hpT, R2 _ _ _ (hb p hpT) hp⟩

variable {G : Type} [Group G]

theorem core_five
    {x : G} {T Q S K : Subgroup G}
    (hxS : x ∈ S) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hTS : T ≤ S) (hTC : T ≤ centralizer ({x} : Set G))
    (hTcent : ∀ s ∈ S, s * x = x * s → s ∈ T)
    (hQT : Q ≤ T) (hQ2 : ∀ q ∈ Q, q * q = 1)
    (hQX : ∀ q ∈ Q, q ≠ 1 → q ≠ x → IsConj x q)
    (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5))
    (hι1 : ((ι (xC x) : Fgrp 5) : Amb 5) = x0 5)
    (hιQ : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q))
    (hιT : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp 5) : Amb 5) ∈ T5)
    (hK : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ K ↔
      Perm.sign ((ι c : Fgrp 5) : Amb 5).1 = 1 ∧ ((ι c : Fgrp 5) : Amb 5).2 = 1)
    (ψ : ↥S →* Perm (Fin 9)) (hψinj : Function.Injective ψ) (hψS0 : ∀ s, ψ s ∈ S0)
    (hψsurj : ∀ p ∈ S0, ∃ s, ψ s = p) (hψx : ψ ⟨x, hxS⟩ = emb 5 f1)
    (hψconj : ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G) →
      numMoved (ψ u) = numMoved (ψ v)) :
    ∃ g : G, g * g = 1 ∧ ∀ q ∈ Q, g * q * g⁻¹ ∈ K := by
  classical
  have hTR : ∀ s : ↥S, (s : G) ∈ T ↔ ψ s ∈ R5 := by
    intro s
    have h1 : (s : G) ∈ T ↔ (s : G) * x = x * (s : G) :=
      ⟨fun hs => mem_centralizer_singleton_iff.1 (hTC hs), hTcent s s.2⟩
    have h2 : (s : G) * x = x * (s : G) ↔ ψ s * emb 5 f1 = emb 5 f1 * ψ s := by
      rw [← hψx, ← map_mul, ← map_mul]
      constructor
      · intro h
        exact congrArg ψ (Subtype.ext h)
      · intro h
        exact congrArg Subtype.val (hψinj h)
    rw [h1, h2]
    exact cent_S0 (hψS0 s)
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨Rel, hRel⟩ : ∃ Rel : Amb 5 → Amb 5 → Prop, ∀ p r, Rel p r ↔
      (p ∈ T5 ∧ r ∈ T5 ∧ ∃ (s : ↥S) (c : ↥(centralizer ({x} : Set G))), (c : G) = (s : G) ∧
        ((ι c : Fgrp 5) : Amb 5) = p ∧ ψ s = emb 5 r) := ⟨_, fun _ _ => Iff.rfl⟩
  have hdom : ∀ p r, Rel p r → p ∈ T5 ∧ r ∈ T5 := fun p r h => ((hRel p r).1 h).imp id And.left
  have R1 : ∀ p ∈ T5, ∃ r, Rel p r := by
    intro p hp
    have hpF : p ∈ Fgrp 5 := T5_le_Fgrp hp
    set c : ↥(centralizer ({x} : Set G)) := ι.symm ⟨p, hpF⟩ with hc
    have hιc : ((ι c : Fgrp 5) : Amb 5) = p := by rw [hc, MulEquiv.apply_symm_apply]
    have hcT : (c : G) ∈ T := (hιT c).2 (by rw [hιc]; exact hp)
    set s : ↥S := ⟨(c : G), hTS hcT⟩ with hs
    have hsT : (s : G) ∈ T := hcT
    obtain ⟨r, hr, hre⟩ := mem_R5.1 ((hTR s).1 hsT)
    exact ⟨r, (hRel p r).2 ⟨hp, hr, s, c, rfl, hιc, hre.symm⟩⟩
  have R2 : ∀ p r r', Rel p r → Rel p r' → r = r' := by
    intro p r r' h h'
    obtain ⟨-, -, s, c, hsc, hcp, hs⟩ := (hRel p r).1 h
    obtain ⟨-, -, s', c', hsc', hcp', hs'⟩ := (hRel p r').1 h'
    have hcc : c = c' := ι.injective (Subtype.ext (hcp.trans hcp'.symm))
    have hss : s = s' := Subtype.ext (hsc.symm.trans ((congrArg Subtype.val hcc).trans hsc'))
    apply emb_injective 5
    rw [← hs, ← hs', hss]
  have R3 : ∀ p q r r', Rel p r → Rel q r' → Rel (p * q) (r * r') := by
    intro p q r r' h h'
    obtain ⟨hp, hr, s, c, hsc, hcp, hs⟩ := (hRel p r).1 h
    obtain ⟨hq, hr', s', c', hsc', hcp', hs'⟩ := (hRel q r').1 h'
    refine (hRel _ _).2 ⟨mul_mem hp hq, mul_mem hr hr', s * s', c * c', ?_, ?_, ?_⟩
    · show (c : G) * (c' : G) = (s : G) * (s' : G)
      rw [hsc, hsc']
    · rw [map_mul, Subgroup.coe_mul, hcp, hcp']
    · rw [map_mul, map_mul, hs, hs']
  have R4 : ∀ p q r, Rel p r → Rel q r → p = q := by
    intro p q r h h'
    obtain ⟨-, -, s, c, hsc, hcp, hs⟩ := (hRel p r).1 h
    obtain ⟨-, -, s', c', hsc', hcp', hs'⟩ := (hRel q r).1 h'
    have hss : s = s' := hψinj (hs.trans hs'.symm)
    have hcc : c = c' := Subtype.ext (hsc.trans ((congrArg Subtype.val hss).trans hsc'.symm))
    rw [← hcp, ← hcp', hcc]
  have R5 : ∀ r ∈ T5, ∃ p, Rel p r := by
    intro r hr
    have hrS : emb 5 r ∈ S0 := R5_le_S0 (mem_R5.2 ⟨r, hr, rfl⟩)
    obtain ⟨s, hs⟩ := hψsurj _ hrS
    have hsT : (s : G) ∈ T := (hTR s).2 (by rw [hs]; exact mem_R5.2 ⟨r, hr, rfl⟩)
    set c : ↥(centralizer ({x} : Set G)) := ⟨(s : G), hTC hsT⟩ with hc
    have hcT : (c : G) ∈ T := hsT
    exact ⟨((ι c : Fgrp 5) : Amb 5), (hRel _ _).2 ⟨(hιT c).1 hcT, hr, s, c, rfl, rfl, hs⟩⟩
  obtain ⟨b, hb, hbR⟩ := exists_aut_of_rel Rel hdom R1 R2 R3 R4 R5
  have hf1 : f1 ∈ T5 := f1_mem_T5
  have H1 : b f1 = f1 :=
    R2 _ _ _ (hbR f1 hf1) ((hRel _ _).2 ⟨hf1, hf1, ⟨x, hxS⟩, xC x, rfl, hι1, hψx⟩)
  have hord : ∀ (s : ↥S) (c : ↥(centralizer ({x} : Set G))) (w : Amb 5), (c : G) = (s : G) →
      ((ι c : Fgrp 5) : Amb 5) = w → w * w = 1 → w ≠ 1 → orderOf s = 2 := by
    intro s c w hsc hcw hww hw1
    have hcc : c * c = 1 := by
      apply ι.injective
      rw [map_mul, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_mul, hcw, hww]
      rfl
    have hss : s * s = 1 := Subtype.ext (by
      show (s : G) * (s : G) = 1
      rw [← hsc]
      exact congrArg Subtype.val hcc)
    have hs1 : s ≠ 1 := by
      intro h
      apply hw1
      have : c = 1 := Subtype.ext (by rw [hsc, h]; rfl)
      rw [← hcw, this, map_one]
      rfl
    exact orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have H2 : ∀ w ∈ T5, ∀ w' ∈ T5, w * w = 1 → w ≠ 1 → w' * w' = 1 → w' ≠ 1 →
      (∃ g ∈ Fgrp 5, g * w * g⁻¹ = w') → nmE (b w) = nmE (b w') := by
    intro w hw w' hw' hww hw1 hww' hw1' ⟨g, hg, hgw⟩
    obtain ⟨-, -, s, c, hsc, hcw, hs⟩ := (hRel w (b w)).1 (hbR w hw)
    obtain ⟨-, -, s', c', hsc', hcw', hs'⟩ := (hRel w' (b w')).1 (hbR w' hw')
    have hconj : IsConj (s : G) (s' : G) := by
      set d : ↥(centralizer ({x} : Set G)) := ι.symm ⟨g, hg⟩ with hd
      have hdg : ((ι d : Fgrp 5) : Amb 5) = g := by rw [hd, MulEquiv.apply_symm_apply]
      have hdc : d * c * d⁻¹ = c' := by
        apply ι.injective
        apply Subtype.ext
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          hdg, hcw, hcw']
        exact hgw
      refine isConj_iff.2 ⟨(d : G), ?_⟩
      rw [← hsc, ← hsc']
      have := congrArg Subtype.val hdc
      simpa using this
    have := hψconj s s' (hord s c w hsc hcw hww hw1) (hord s' c' w' hsc' hcw' hww' hw1') hconj
    rw [hs, hs'] at this
    exact this
  have H3 : ∀ q ∈ T5, q.1 = 1 → q ≠ 1 → nmE (b q) = 4 := by
    intro q hq hq1 hq1'
    obtain ⟨-, -, s, c, hsc, hcq, hs⟩ := (hRel q (b q)).1 (hbR q hq)
    have hcQ : (c : G) ∈ Q := (hιQ c).1 (by rw [hcq]; exact hq1)
    have hsQ : (s : G) ∈ Q := hsc ▸ hcQ
    have hs1 : (s : G) ≠ 1 := by
      intro h
      apply hq1'
      have : c = 1 := Subtype.ext (by rw [hsc, h]; rfl)
      rw [← hcq, this, map_one]
      rfl
    have hx_order : orderOf (⟨x, hxS⟩ : ↥S) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    have hs_order : orderOf s = 2 :=
      orderOf_eq_prime (by rw [sq]; exact Subtype.ext (hQ2 _ hsQ))
        (fun h => hs1 (congrArg Subtype.val h))
    by_cases hsx : (s : G) = x
    · have hs' : s = ⟨x, hxS⟩ := Subtype.ext hsx
      rw [hs', hψx] at hs
      show numMoved (emb 5 (b q)) = 4
      rw [← hs]
      exact nmE_f1
    · have hconj := hQX (s : G) hsQ hs1 hsx
      have := hψconj ⟨x, hxS⟩ s hx_order hs_order hconj
      rw [hψx, hs] at this
      exact this.symm.trans nmE_f1
  have hmodel := model_five b hb H1 H2 H3
  obtain ⟨g₀, hg₀⟩ := hψsurj _ a0_mem_S0
  refine ⟨(g₀ : G), ?_, ?_⟩
  · have : g₀ * g₀ = 1 := hψinj (by rw [map_mul, hg₀, a0_sq, map_one])
    exact congrArg Subtype.val this
  · intro q hq
    have hqT : q ∈ T := hQT hq
    set qS : ↥S := ⟨q, hTS hqT⟩ with hqS
    have hqC : q ∈ centralizer ({x} : Set G) := hTC hqT
    set cq : ↥(centralizer ({x} : Set G)) := ⟨q, hqC⟩ with hcq
    set p : Amb 5 := ((ι cq : Fgrp 5) : Amb 5) with hp
    have hpT : p ∈ T5 := (hιT cq).1 hqT
    have hp1 : p.1 = 1 := (hιQ cq).2 hq
    obtain ⟨r, hr, hre⟩ := mem_R5.1 ((hTR qS).1 hqT)
    have hRelp : Rel p r := (hRel _ _).2 ⟨hpT, hr, qS, cq, rfl, rfl, hre.symm⟩
    have hbp : b p = r := R2 _ _ _ (hbR p hpT) hRelp
    obtain ⟨v, hv, hv2, hvconj⟩ := hmodel p hpT hp1
    obtain ⟨-, -, sv, cv, hsvc, hcvv, hsv⟩ := (hRel v (b v)).1 (hbR v hv)
    have hψgq : ψ (g₀ * qS * g₀⁻¹) = ψ sv := by
      rw [map_mul, map_mul, map_inv, hg₀, ← hre, ← hbp, hvconj, hsv]
    have hgs : g₀ * qS * g₀⁻¹ = sv := hψinj hψgq
    have hgq : (g₀ : G) * q * (g₀ : G)⁻¹ = (cv : G) :=
      calc (g₀ : G) * q * (g₀ : G)⁻¹ = ((g₀ * qS * g₀⁻¹ : ↥S) : G) := rfl
        _ = (sv : G) := congrArg Subtype.val hgs
        _ = (cv : G) := hsvc.symm
    rw [hgq, hK cv, hcvv]
    exact ⟨T5_sign_of_snd hv hv2, hv2⟩

end CFSG.GH74.GLS.C3.Prop121
