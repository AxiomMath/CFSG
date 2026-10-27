module

public import CFSG.GH74.GLS.C3.Layer2.L5Pat
public import CFSG.GH74.GLS.C3.Layer2.L5Model
public import CFSG.GH74.GLS.C3.Layer2.Terminal

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem exists_aut_of_rel' (Rel : Amb 5 → Amb 5 → Prop)
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

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem Psi5.nm_four_or_eight
    {hxS : x ∈ S} {hvS : x * (a * x * a⁻¹) ∈ S}
    {ψ : ↥S →* Perm (Fin 9)} (hψ : Psi5 x a S hxS hvS ψ) {s : ↥S} (hs : orderOf s = 2) :
    numMoved (ψ s) = 4 ∨ numMoved (ψ s) = 8 := by
  have h1 : orderOf (ψ s) = 2 := by rw [orderOf_injective ψ hψ.inj s]; exact hs
  let g : alternatingGroup (Fin 9) := ⟨ψ s, S0_le_alt (hψ.mem s)⟩
  have hg : orderOf g = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h1
  exact numMoved_eq_of_involution_alternating 9 (by norm_num) g hg

theorem hQX_five
    (hG4 : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a)
    {hxS : x ∈ S} {hvS : x * (a * x * a⁻¹) ∈ S}
    {ψ : ↥S →* Perm (Fin 9)} (hψ : Psi5 x a S hxS hvS ψ) :
    ∀ q ∈ Q, q ≠ 1 → q ≠ x → IsConj x q := by
  intro q hqQ hq1 hqx
  have hTS : T ≤ S := h.T_lt_S.le
  have hqT : q ∈ T := h.Q_le_T hqQ
  have hqS : q ∈ S := hTS hqT
  let qS : ↥S := ⟨q, hqS⟩
  let xS : ↥S := ⟨x, hxS⟩
  let vS : ↥S := ⟨x * (a * x * a⁻¹), hvS⟩
  have hqsq : qS * qS = 1 := Subtype.ext (by
    show q * q = 1
    rw [← sq]
    exact h.Q_sq hqQ)
  have hq2 : orderOf qS = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hqsq) (fun hc => hq1 (congrArg Subtype.val hc))
  have hxsq : xS * xS = 1 := Subtype.ext (by
    show x * x = 1
    rw [← sq]
    exact h.x_sq)
  have hx2 : orderOf xS = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hxsq) (fun hc => h.x_ne_one (congrArg Subtype.val hc))
  have hvsq : vS * vS = 1 := Subtype.ext (by
    show x * (a * x * a⁻¹) * (x * (a * x * a⁻¹)) = 1
    exact L4.v_mul_self h)
  have hv2 : orderOf vS = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hvsq) (fun hc => L4.v_ne_one h (congrArg Subtype.val hc))
  have hnx : numMoved (ψ xS) = 4 := by
    show numMoved (ψ ⟨x, hxS⟩) = 4
    rw [hψ.x_eq]
    exact nmE_f1
  have hnv : numMoved (ψ vS) = 8 := by
    show numMoved (ψ ⟨x * (a * x * a⁻¹), hvS⟩) = 8
    rw [hψ.v_eq]
    exact numMoved_yS
  rcases hψ.nm_four_or_eight hq2 with h4 | h8
  · exact ((hψ.conj qS xS hq2 hx2).2 (h4.trans hnx.symm)).symm
  · exfalso
    have hqv : IsConj (q : G) (x * (a * x * a⁻¹)) := (hψ.conj qS vS hq2 hv2).2 (h8.trans hnv.symm)
    have hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t := by
      obtain ⟨y, hyT, -, -, q', hq', hyq⟩ := h.fiveCase rfl
      exact ⟨y, hyT, q', hq', hyq⟩
    have hle := h.factorization_centralizer_le (by norm_num) hG4 hnt q hqQ hq1
    obtain ⟨e⟩ := nonempty_centralizer_equiv_of_isConj hqv
    have hcard := Nat.card_congr e.toEquiv
    have hSle : T ⊔ zpowers a ≤ S := sup_le hTS (zpowers_le.2 h.a_mem.1)
    have hp : IsPGroup 2 ↥(T ⊔ zpowers a) := IsPGroup.to_le h.sylowS.isPGroup hSle
    have haS1 : a ∈ T ⊔ zpowers a := (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)
    have hlt : T < T ⊔ zpowers a := lt_of_le_of_ne le_sup_left (fun heq => by
      rw [← heq] at haS1
      exact h.a_mem.2.2.1 haS1)
    have hcard' := Subgroup.card_lt_of_lt hlt
    have hT32 : Nat.card T = 2 ^ ((Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :=
      h.sylowT.card_eq
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk, hT32] at hcard'
    have hk6 : (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 + 1 ≤ k := by
      by_contra hk6
      have : 2 ^ k ≤ 2 ^ ((Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h7 : 2 ^ ((Nat.card ↥(centralizer ({x} : Set G))).factorization 2 + 1) ∣
        Nat.card ↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) :=
      (pow_dvd_pow 2 hk6).trans (hk ▸ Subgroup.card_dvd_of_le h.sup_le_centralizer_v)
    have hne : Nat.card ↥(centralizer ({q} : Set G)) ≠ 0 := Nat.card_pos.ne'
    rw [← hcard] at h7
    have h8' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 h7
    omega

theorem psi_mem_R5_iff (h : IsAConfig 5 x K T Q S a) {hxS : x ∈ S}
    {hvS : x * (a * x * a⁻¹) ∈ S} {ψ : ↥S →* Perm (Fin 9)} (hψ : Psi5 x a S hxS hvS ψ)
    (s : ↥S) : (s : G) ∈ T ↔ ψ s ∈ R5 := by
  have hTS : T ≤ S := h.T_lt_S.le
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  have hTinf : S ⊓ centralizer ({x} : Set G) = T :=
    h.sylowT.eq_of_le (le_inf hTS h.T_le_C) inf_le_right h.sylowS.isPGroup.to_inf_left
  have hTcent : ∀ s ∈ S, s * x = x * s → s ∈ T := fun s hs hc => by
    rw [← hTinf]
    exact ⟨hs, mem_centralizer_singleton_iff.2 hc⟩
  have h1 : (s : G) ∈ T ↔ (s : G) * x = x * (s : G) :=
    ⟨fun hs => mem_centralizer_singleton_iff.1 (hTC hs), hTcent s s.2⟩
  have h2 : (s : G) * x = x * (s : G) ↔ ψ s * emb 5 f1 = emb 5 f1 * ψ s := by
    rw [← hψ.x_eq, ← map_mul, ← map_mul]
    constructor
    · intro h
      exact congrArg ψ (Subtype.ext h)
    · intro h
      exact congrArg Subtype.val (hψ.inj h)
  rw [h1, h2]
  exact cent_S0 (hψ.mem s)

theorem exists_adm
    (h : IsAConfig 5 x K T Q S a)
    {hxS : x ∈ S} {hvS : x * (a * x * a⁻¹) ∈ S}
    (hQX : ∀ q ∈ Q, q ≠ 1 → q ≠ x → IsConj x q)
    (ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5))
    (hι1 : ((ι (xC x) : Fgrp 5) : Amb 5) = x0 5)
    (hιQ : ∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q))
    (hιT : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp 5) : Amb 5) ∈ T5)
    {ψ : ↥S →* Perm (Fin 9)} (hψ : Psi5 x a S hxS hvS ψ) :
    ∃ b : Amb 5 → Amb 5, Adm b ∧ ∀ (s : ↥S) (c : ↥(centralizer ({x} : Set G))),
      (c : G) = (s : G) → (c : G) ∈ T → ψ s = emb 5 (b ((ι c : Fgrp 5) : Amb 5)) := by
  classical
  have hTS : T ≤ S := h.T_lt_S.le
  have hTC : T ≤ centralizer ({x} : Set G) := h.T_le_C
  have hx2 : x * x = 1 := by rw [← sq]; exact h.x_sq
  have hx1 : x ≠ 1 := h.x_ne_one
  have hψconj : ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G) →
      numMoved (ψ u) = numMoved (ψ v) := fun u v hu hv huv => (hψ.conj u v hu hv).1 huv
  have hψx : ψ ⟨x, hxS⟩ = emb 5 f1 := hψ.x_eq
  have hTR : ∀ s : ↥S, (s : G) ∈ T ↔ ψ s ∈ R5 := psi_mem_R5_iff h hψ
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
    have hss : s = s' := hψ.inj (hs.trans hs'.symm)
    have hcc : c = c' := Subtype.ext (hsc.trans ((congrArg Subtype.val hss).trans hsc'.symm))
    rw [← hcp, ← hcp', hcc]
  have R5 : ∀ r ∈ T5, ∃ p, Rel p r := by
    intro r hr
    have hrS : emb 5 r ∈ S0 := R5_le_S0 (mem_R5.2 ⟨r, hr, rfl⟩)
    obtain ⟨s, hs⟩ := hψ.surj _ hrS
    have hsT : (s : G) ∈ T := (hTR s).2 (by rw [hs]; exact mem_R5.2 ⟨r, hr, rfl⟩)
    set c : ↥(centralizer ({x} : Set G)) := ⟨(s : G), hTC hsT⟩ with hc
    have hcT : (c : G) ∈ T := hsT
    exact ⟨((ι c : Fgrp 5) : Amb 5), (hRel _ _).2 ⟨(hιT c).1 hcT, hr, s, c, rfl, rfl, hs⟩⟩
  obtain ⟨b, hb, hbR⟩ := exists_aut_of_rel' Rel hdom R1 R2 R3 R4 R5
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
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => by rw [← sq]; exact h.Q_sq hq
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
  refine ⟨b, ⟨hb, H1, H2, H3⟩, ?_⟩
  intro s c hsc hcT
  have hp : ((ι c : Fgrp 5) : Amb 5) ∈ T5 := (hιT c).1 hcT
  obtain ⟨-, -, s', c', hsc', hcp', hs'⟩ := (hRel _ (b ((ι c : Fgrp 5) : Amb 5))).1 (hbR _ hp)
  have hcc : c' = c := ι.injective (Subtype.ext hcp')
  have hss : s' = s := Subtype.ext (hsc'.symm.trans ((congrArg Subtype.val hcc).trans hsc))
  rw [← hss]
  exact hs'

end CFSG.GH74.GLS.C3.Layer2.L5
