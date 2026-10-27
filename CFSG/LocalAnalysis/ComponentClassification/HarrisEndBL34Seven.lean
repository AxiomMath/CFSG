module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Layer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSeven

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

theorem conj_r₂_of_card_ge {r : PSL3Four.R}
    (hr2 : orderOf r = 2) (hrS : (r : Equiv.Perm (Fin 42)) ∉ PSL3Four.S)
    (h168 : 168 ≤ Nat.card ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S)) :
    ∃ c ∈ PSL3Four.R, (r : Equiv.Perm (Fin 42)) = c * PSL3Four.r₂ * c⁻¹ := by
  rcases (PSL3Four.orderOf_eq_two_iff r).mp hr2 with h | h | h | h
  · exact absurd (PSL3Four.mem_S_of_isConj₁ h) hrS
  · exact PSL3Four.eq_conj_of_isConj h
  · exfalso
    obtain ⟨c, hc, hrc⟩ := PSL3Four.eq_conj_of_isConj h
    obtain ⟨ψ⟩ := nonempty_centralizer_conj_equiv hc hrc
    have h60 : Nat.card ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 60 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact PSL3Four.card_C₃
    omega
  · exfalso
    obtain ⟨c, hc, hrc⟩ := PSL3Four.eq_conj_of_isConj h
    obtain ⟨ψ⟩ := nonempty_centralizer_conj_equiv hc hrc
    have h72 : Nat.card ↥(centralizer {(r : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 72 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact PSL3Four.card_C₄
    omega

end EndB

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem KBar_le (hL : LLayer hs π) :
    KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
  rw [← hL.h412.layerIn_layer_centralizer]
  exact map_subtype_le _

theorem pi_injOn_KBar (hL : LLayer hs π) {a b : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
    z ^ j)))} (ha : (a : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hb : (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) (hab : π a = π b) : a = b := by
  have hK := hs.lieModel_KBar hL.h412
  have := isSimpleGroup_of_lieModel_psl2 hK
  obtain ⟨u, v, huv⟩ := nonabelian_of_lieModel_psl2 hK
  have hZ : center ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) with h | h
    · exact h
    · exact absurd ((mem_center_iff.mp (h ▸ mem_top u) v).symm) huv
  have hc : a⁻¹ * b ∈ center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [← hL.ker, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hk : (⟨(a⁻¹ * b : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))),
      by simpa using mul_mem (inv_mem ha) hb⟩ :
        ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∈
      center ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    have hgE : (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := hs.KBar_le_layer g.2
    have := congrArg Subtype.val (mem_center_iff.mp hc ⟨g, hgE⟩)
    simpa using this
  rw [hZ, mem_bot] at hk
  have h1 : ((a⁻¹ * b : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := congrArg Subtype.val hk
  have h2 : a⁻¹ * b = 1 := Subtype.ext h1
  rw [inv_mul_eq_one] at h2
  exact h2

theorem pi_KBar_mem (hL : LLayer hs π)
    {a : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (ha : (a : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j}) :
    ((π a : PSL3Four.S) : Equiv.Perm (Fin 42)) ∈
      centralizer {((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42))} ⊓
        PSL3Four.S := by
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, (π a).2⟩
  have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2
  have h := hL.rho_conj (hs.setup.tBar i j) a a (by rw [← hc, mul_inv_cancel_right])
  calc ((π a : PSL3Four.S) : Equiv.Perm (Fin 42)) *
        ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
      ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42)) *
        (π a : Equiv.Perm (Fin 42)) *
        ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42))⁻¹ *
        ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42)) := by rw [h]
    _ = _ := by group

theorem le_card_centralizer_rho_t (hL : LLayer hs π) :
    Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      Nat.card ↥(centralizer {((hL.rho (hs.setup.tBar i j) : PSL3Four.R) :
        Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) := by
  let φ : ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) →
      ↥(centralizer {((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42))} ⊓
        PSL3Four.S) := fun k =>
    ⟨π ⟨k, hs.KBar_le_layer k.2⟩, hL.pi_KBar_mem (hL.KBar_le k.2)⟩
  refine Nat.card_le_card_of_injective φ fun a b hab => ?_
  have h0 : ((φ a : _) : Equiv.Perm (Fin 42)) = φ b := congrArg Subtype.val hab
  have h1 : π ⟨a, hs.KBar_le_layer a.2⟩ = π ⟨b, hs.KBar_le_layer b.2⟩ := Subtype.ext h0
  have h2 := hL.pi_injOn_KBar a.2 b.2 h1
  have h3 : ((⟨a, hs.KBar_le_layer a.2⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
      z ^ j)))) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = (⟨b, hs.KBar_le_layer b.2⟩ :
        ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := congrArg Subtype.val h2
  exact Subtype.ext h3

theorem rho_t_conj (hL : LLayer hs π) :
    ∃ c ∈ PSL3Four.R, ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
      c * PSL3Four.r₂ * c⁻¹ := by
  obtain ⟨h2, hS⟩ := hL.rho_t_facts
  refine conj_r₂_of_card_ge h2 hS ((le_card_of_lieModel_psl2 hs.p_ne_two hs.sixteen_dvd
    (hs.lieModel_KBar hL.h412)).trans hL.le_card_centralizer_rho_t)

theorem card_centralizer_rho_t (hL : LLayer hs π) :
    Nat.card ↥(centralizer {((hL.rho (hs.setup.tBar i j) : PSL3Four.R) :
      Equiv.Perm (Fin 42))} ⊓ PSL3Four.S) = 168 := by
  obtain ⟨c, hc, hrc⟩ := hL.rho_t_conj
  obtain ⟨ψ⟩ := nonempty_centralizer_conj_equiv hc hrc
  rw [Nat.card_congr ψ.toEquiv]
  exact PSL3Four.card_C₂

theorem center_inf_centralizer (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    (x ∈ (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype ∧
      x ∈ centralizer {hs.setup.tBar i j}) ↔
      x ∈ zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have hβZ := hL.h412.lemma46c.2.2 hZ
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hct⟩
    have hcQ : (c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hs.centralizer_layer_eq hL.h412, mem_centralizer_iff]
      intro e he
      have := congrArg Subtype.val (mem_center_iff.mp hc ⟨e, he⟩)
      simpa using this
    rw [← hL.h412.pCore_inf_centralizer]
    exact mem_inf.mpr ⟨hcQ, hct⟩
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨zpow_mem hβZ k, zpow_mem (mem_centralizer_singleton_iff.mpr ?_) k⟩
    exact (mem_center_iff.mp (betaBar_mem_center _) _).symm

theorem card_layer_inf_centralizer (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336 := by
  set H := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j}
    with hH
  set ψ : ↥H →* PSL3Four.S := π.comp (Subgroup.inclusion inf_le_left) with hψ
  have hψa : ∀ h : ↥H, ψ h = π ⟨h, (mem_inf.mp h.2).1⟩ := fun h => rfl
  have hrange : Nat.card ψ.range = 168 := by
    refine le_antisymm ?_ ?_
    · rw [← hL.card_centralizer_rho_t]
      refine Nat.card_le_card_of_injective (fun s : ψ.range => ⟨((s : PSL3Four.S) :
        Equiv.Perm (Fin 42)), ?_⟩) fun a b hab => ?_
      · obtain ⟨h, hh⟩ := s.2
        rw [← hh, hψa]
        exact hL.pi_KBar_mem h.2
      · have h1 := congrArg Subtype.val hab
        simp only at h1
        exact Subtype.ext (Subtype.ext h1)
    · refine (le_card_of_lieModel_psl2 hs.p_ne_two hs.sixteen_dvd
        (hs.lieModel_KBar hL.h412)).trans ?_
      refine Nat.card_le_card_of_injective (fun k : ↥(KBar L (w ^ (orderOf w / 2) * t ^ i *
        z ^ j)) => (⟨ψ ⟨k, hL.KBar_le k.2⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ : ψ.range))
        fun a b hab => ?_
      have h1 : ψ ⟨a, hL.KBar_le a.2⟩ = ψ ⟨b, hL.KBar_le b.2⟩ := congrArg Subtype.val hab
      rw [hψa, hψa] at h1
      have h2 := hL.pi_injOn_KBar a.2 b.2 h1
      have h3 : ((⟨a, hs.KBar_le_layer a.2⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
          z ^ j)))) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = (⟨b, hs.KBar_le_layer b.2⟩ :
            ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := congrArg Subtype.val h2
      exact Subtype.ext h3
  have hker : Nat.card ψ.ker = 2 := by
    have hβ2 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
    have hmem : ∀ h : ↥H, h ∈ ψ.ker ↔ (h : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      intro h
      rw [MonoidHom.mem_ker, hψa, ← MonoidHom.mem_ker, hL.ker, ← hL.center_inf_centralizer hZ]
      constructor
      · intro hc
        exact ⟨⟨_, hc, rfl⟩, (mem_inf.mp h.2).2⟩
      · rintro ⟨⟨c, hc, hce⟩, -⟩
        have : c = ⟨h, (mem_inf.mp h.2).1⟩ := Subtype.ext hce
        rw [← this]
        exact hc
    have heq : Nat.card ψ.ker =
        Nat.card ↥(zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
      refine Nat.card_congr ⟨fun h => ⟨(h : ↥H), (hmem h).mp h.2⟩, fun x => ⟨⟨x, ?_⟩, ?_⟩,
        fun h => rfl, fun x => rfl⟩
      · obtain ⟨hxZ, hxC⟩ := (hL.center_inf_centralizer hZ x).mpr x.2
        obtain ⟨c, -, hce⟩ := hxZ
        exact mem_inf.mpr ⟨hce ▸ c.2, hxC⟩
      · exact (hmem _).mpr x.2
    rw [heq, Nat.card_zpowers, hβ2]
  rw [← Subgroup.card_ker_mul_card_range ψ, hker, hrange]

theorem seven (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    Nat.card ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 168 ∧ p = 7 ∧ f / 2 = 1 ∧
      Nonempty (↥(S ⊓ L) ≃* DihedralGroup (2 ^ 3)) := by
  have hK := card_eq_168_of_lieModel_dvd hs.p_ne_two hs.sixteen_dvd (hs.lieModel_KBar hL.h412)
    (by rw [← hL.card_layer_inf_centralizer hZ]; exact Subgroup.card_dvd_of_le hL.KBar_le)
  obtain ⟨hp7, hf⟩ := eq_seven_of_lieModel_card hs.p_ne_two (hs.lieModel_KBar hL.h412) hK
  obtain ⟨m, -, ⟨e⟩⟩ := hs.setup.dihedral
  have hm := hs.factorization_card_KBar hL.h412 e
  rw [hK, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at hm
  subst hm
  exact ⟨hK, hp7, hf, ⟨e⟩⟩

theorem card_T_le (hL : LLayer hs π) :
    Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set πM := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπM
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hT1 : IsSylowOf 2 T (centralizer ({t} : Set X) ⊓ M) := hs.lemma45.isSylowOf_T
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hTH : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  set Tb := (T.subgroupOf M).map πM with hTb
  have hTp : IsPGroup 2 (T.subgroupOf M) :=
    hT1.isPGroup.of_equiv (subgroupOfEquivOfLe hTM).symm
  have hcardT : Nat.card Tb = Nat.card T := by
    rw [hTb, GSThmB.OddQuot.card_map_of_isPGroup hTp,
      Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv]
  have hTbC : Tb ≤ centralizer {hs.setup.tBar i j} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hgt : g * ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ =
        ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * g :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hTH hg))
    change πM g * πM ⟨t, _⟩ = πM ⟨t, _⟩ * πM g
    rw [← map_mul, ← map_mul, hgt]
  set φ : ↥Tb →* PSL3Four.R := hL.rho.comp Tb.subtype with hφ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map Tb.subtype ≤ zpowers (betaBar β) := by
      rintro _ ⟨g, hg, rfl⟩
      replace hg := MonoidHom.mem_ker.mp hg
      have h1 : (g : MBar β) ∈ pCore 2 (MBar β) ⊓ centralizer {hs.setup.tBar i j} :=
        ⟨(hL.rho_eq_one_iff g).mp hg, hTbC g.2⟩
      rw [hL.h412.pCore_inf_centralizer] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (subtype_injective _), Nat.card_zpowers] at h1
    have h2 : orderOf (betaBar β) ∣ 2 := orderOf_dvd_of_pow_eq_one hs.betaBar_sq
    exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
  have hrange : Nat.card φ.range ≤ 32 := by
    obtain ⟨c, hc, hrc⟩ := hL.rho_t_conj
    have hle : φ.range ≤ centralizer {hL.rho (hs.setup.tBar i j)} := by
      rintro _ ⟨g, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hgt : (g : MBar β) * hs.setup.tBar i j = hs.setup.tBar i j * g :=
        mem_centralizer_singleton_iff.mp (hTbC g.2)
      change hL.rho g * hL.rho (hs.setup.tBar i j) = hL.rho (hs.setup.tBar i j) * hL.rho g
      rw [← map_mul, ← map_mul, hgt]
    have hc' : hL.rho (hs.setup.tBar i j) = ⟨c, hc⟩ * PSL3Four.r₂R * ⟨c, hc⟩⁻¹ := Subtype.ext hrc
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hc', card_centralizer_conj_r₂R] at hdvd
    have hTbp : IsPGroup 2 Tb := hTp.map πM
    exact card_le_32_of_dvd (hTbp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) hdvd
  rw [← hcardT, ← Subgroup.card_ker_mul_card_range φ]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 32 := Nat.mul_le_mul hker hrange
    _ = 64 := by norm_num

theorem orderOf_w (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    orderOf w = 2 := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := hL.seven hZ
  have h := hL.card_T_le
  rw [hs.card_T_eq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h
  norm_num at h
  have hw := hs.setup.orderOf_w_eq
  have hw1 : orderOf w ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite w)
  have hw2 : orderOf w ≠ 1 := fun h => hs.setup.w_ne_one (orderOf_eq_one_iff.mp h)
  omega

theorem card_T (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) = 64 := by
  obtain ⟨-, -, -, ⟨e⟩⟩ := hL.seven hZ
  rw [hs.card_T_eq, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hL.orderOf_w hZ]
  norm_num

theorem card_S_le (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    Nat.card S ≤ 128 := by
  obtain ⟨-, -, -, -, hcardS, -⟩ :=
    hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3
  rw [hL.card_T hZ] at hcardS
  omega

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
