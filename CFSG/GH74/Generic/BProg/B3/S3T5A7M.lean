module

public import CFSG.GH74.Generic.BProg.B3.S3T5A7
public import CFSG.GH74.Generic.BProg.B3.S3T5Q8
public import CFSG.GH74.Generic.BProg.B2.PumpupTwoA7GH
public import CFSG.GH74.KGroups.TwoA7Cover

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

namespace W

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem exists_two_ne_one_of_two_lt {X : Type*} [Group X] {U : Subgroup X} [Finite U]
    (hU : 2 < Nat.card U) : ∃ a ∈ U, ∃ c ∈ U, a ≠ 1 ∧ c ≠ 1 ∧ a ≠ c := by
  classical
  have : Fintype U := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hU
  obtain ⟨x, y, w, hxy, hxw, hyw⟩ := Fintype.two_lt_card_iff.1 hU
  by_cases hx : (x : X) = 1
  · exact ⟨y, y.2, w, w.2, fun h => hxy (Subtype.ext (hx.trans h.symm)),
      fun h => hxw (Subtype.ext (hx.trans h.symm)), fun h => hyw (Subtype.ext h)⟩
  · by_cases hy : (y : X) = 1
    · exact ⟨x, x.2, w, w.2, hx, fun h => hyw (Subtype.ext (hy.trans h.symm)),
        fun h => hxw (Subtype.ext h)⟩
    · exact ⟨x, x.2, y, y.2, hx, hy, fun h => hxy (Subtype.ext h)⟩

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {b : G} {D J : Subgroup G}

theorem mem_of_twoA7 (hG4 : Gen4 G) (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hcov : IsDoubleCoverOfAlt (kBar J) 7) : b ∈ J := by
  classical
  obtain ⟨-, hDel, hDr⟩ := h.D_le
  obtain ⟨hDc, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have h3 : 2 < Nat.card ↥D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥D := Nat.pow_le_pow_right (by norm_num) hDr
  obtain ⟨d₁, hd₁D, d₂, hd₂D, hd₁1, hd₂1, hd12⟩ := exists_two_ne_one_of_two_lt h3
  have hd12D : d₁ * d₂ ∈ D := D.mul_mem hd₁D hd₂D
  have hd121 : d₁ * d₂ ≠ 1 := by
    intro h1
    apply hd12
    calc d₁ = d₁ * (d₂ * d₂) := by rw [hDsq d₂ hd₂D, mul_one]
      _ = (d₁ * d₂) * d₂ := (mul_assoc _ _ _).symm
      _ = d₂ := by rw [h1, one_mul]
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_inner_of_twoA7 h hBel hcov hd₁D hd₁1
  obtain ⟨ℓ₂, hℓ₂⟩ := exists_inner_of_twoA7 h hBel hcov hd₂D hd₂1
  have hℓ12 : Th2.Obs.barAct J ⟨d₁ * d₂, h.D_norm hd12D⟩ = MulAut.conj (ℓ₁ * ℓ₂) := by
    rw [(MulAut.conj : kBar J →* MulAut (kBar J)).map_mul ℓ₁ ℓ₂, ← hℓ₁, ← hℓ₂, ← map_mul]
    rfl
  have hconj1 : ∀ ℓ : kBar J, ℓ ∈ center (kBar J) → MulAut.conj ℓ = 1 := fun ℓ hℓ => by
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.mp hℓ x),
      mul_inv_cancel_right]
  have hfaith : ∀ {d : G} (hdD : d ∈ D), d ≠ 1 → ∀ {ℓ : kBar J},
      Th2.Obs.barAct J ⟨d, h.D_norm hdD⟩ = MulAut.conj ℓ → ℓ ∉ center (kBar J) := by
    intro d hdD hd1 ℓ hℓ hc
    rw [hconj1 ℓ hc] at hℓ
    exact h.D_faith d hdD hd1 ((Th2.Obs.barAct_eq_one_iff ⟨d, h.D_norm hdD⟩).1 hℓ)
  set N₀ : Subgroup G := normalizer (J : Set G) ⊓ centralizer ({b} : Set G) with hN₀
  have hJC : J ≤ centralizer ({b} : Set G) := h.comp.1
  have hJN : J ≤ N₀ := le_inf Subgroup.le_normalizer hJC
  have hDN₀ : ∀ {d : G}, d ∈ D → d ∈ N₀ := fun hd => ⟨h.D_norm hd, D_le_centralizer h hd⟩
  have hbCJ : b ∈ centralizer (J : Set G) := Subgroup.mem_centralizer_iff.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJC hl)
  have hbN₀ : b ∈ N₀ :=
    ⟨Subgroup.centralizer_le_normalizer _ hbCJ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set O₀ : Subgroup ↥N₀ := (pPrimeCoreOf 2 J).subgroupOf N₀ with hO₀
  have hO₀n : O₀.Normal := ⟨fun n hn g => by
    rw [hO₀, Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ normalizer ((pPrimeCoreOf 2 J : Subgroup G) : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.mem_inf.mp g.2).1
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hn⟩
  have hYg : Gen4 (↥N₀ ⧸ O₀) := Gen4.quotient O₀ (Gen4.subgroup N₀ hG4)
  set π : ↥N₀ →* ↥N₀ ⧸ O₀ := QuotientGroup.mk' O₀ with hπ
  set ψJ : ↥J →* ↥N₀ ⧸ O₀ := π.comp (Subgroup.inclusion hJN) with hψJ
  have hker : pPrimeCore 2 ↥J ≤ ψJ.ker := fun l hl => by
    rw [MonoidHom.mem_ker]
    show π (Subgroup.inclusion hJN l) = 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO₀, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_of_mem J.subtype hl
  set ι : kBar J →* ↥N₀ ⧸ O₀ := QuotientGroup.lift (pPrimeCore 2 ↥J) ψJ hker with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : π (Subgroup.inclusion hJN l) = 1 := hq
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hO₀, Subgroup.mem_subgroupOf] at h1
    obtain ⟨l', hl', he⟩ := Subgroup.mem_map.mp h1
    have hll : l' = l := Subtype.ext he
    rw [QuotientGroup.eq_one_iff, ← hll]
    exact hl'
  have hact : ∀ {d : G} (hdD : d ∈ D) {ℓ : kBar J},
      Th2.Obs.barAct J ⟨d, h.D_norm hdD⟩ = MulAut.conj ℓ →
      ∀ q, π ⟨d, hDN₀ hdD⟩ * ι q * (π ⟨d, hDN₀ hdD⟩)⁻¹ = ι (ℓ * q * ℓ⁻¹) := by
    intro d hdD ℓ hℓ q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : ℓ * (QuotientGroup.mk l : kBar J) * ℓ⁻¹ =
        Th2.Obs.barAct J ⟨d, h.D_norm hdD⟩ (QuotientGroup.mk l) := by
      rw [hℓ, MulAut.conj_apply]
    have h2 : Th2.Obs.barAct J ⟨d, h.D_norm hdD⟩ (QuotientGroup.mk l) =
        QuotientGroup.mk ⟨d * l * d⁻¹, Th2.Obs.normalizer_conj_mem d (h.D_norm hdD) l l.2⟩ :=
      C3.Layer1.Back.actHom_mk _ _ _
    rw [h1, h2]
    rfl
  have hsq : ∀ {d : G} (hdD : d ∈ D), π ⟨d, hDN₀ hdD⟩ * π ⟨d, hDN₀ hdD⟩ = 1 := by
    intro d hdD
    rw [← map_mul]
    have : (⟨d, hDN₀ hdD⟩ : ↥N₀) * ⟨d, hDN₀ hdD⟩ = 1 := Subtype.ext (hDsq d hdD)
    rw [this, map_one]
  have hcomm : π ⟨d₁, hDN₀ hd₁D⟩ * π ⟨d₂, hDN₀ hd₂D⟩ = π ⟨d₂, hDN₀ hd₂D⟩ * π ⟨d₁, hDN₀ hd₁D⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hDc d₁ hd₁D d₂ hd₂D)
  have hβc : ∀ y : ↥N₀ ⧸ O₀, y * π ⟨b, hbN₀⟩ = π ⟨b, hbN₀⟩ * y := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O₀ y
    show π n * π ⟨b, hbN₀⟩ = π ⟨b, hbN₀⟩ * π n
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp n.2).2)
  have hb2 : b * b = 1 := by rw [← pow_two, ← h.b_ord, pow_orderOf_eq_one]
  have hβ2 : π ⟨b, hbN₀⟩ * π ⟨b, hbN₀⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hbN₀⟩ : ↥N₀) * ⟨b, hbN₀⟩ = 1 := Subtype.ext hb2
    rw [this, map_one]
  obtain ⟨π₀, z, hz, hzc⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover hcov
  have hmem := mem_range_of_inner_four hYg ι hιinj hz.ne_one ((hzc z).2 (Or.inr rfl))
    (fun q hq => hz.eq_one_or_eq_z_of_sq_eq_one hq) (fun q hq => (hzc q).1 hq)
    (hsq hd₁D) (hsq hd₂D) hcomm (hact hd₁D hℓ₁) (hact hd₂D hℓ₂) (hfaith hd₁D hd₁1 hℓ₁)
    (hfaith hd₂D hd₂1 hℓ₂) (hfaith hd12D hd121 hℓ12) hβc hβ2
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : π (Subgroup.inclusion hJN l) = π ⟨b, hbN₀⟩ := hq
  rw [hπ, QuotientGroup.mk'_eq_mk'] at h1
  obtain ⟨o, ho, hoe⟩ := h1
  have hoJ : (o : G) ∈ J := by
    rw [hO₀, Subgroup.mem_subgroupOf] at ho
    exact Subgroup.map_subtype_le (pPrimeCore 2 ↥J) ho
  have hb : b = (l : G) * (o : G) := (congrArg Subtype.val hoe).symm
  rw [hb]
  exact J.mul_mem l.2 hoJ

theorem false_of_twoA7 (hyp : Hyp2 G) (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB3 : 3 ≤ pRank 2 ↥B)
    (hcov : IsDoubleCoverOfAlt (kBar J) 7) : False := by
  have hbJ : b ∈ J := mem_of_twoA7 hyp.gen4 h hBel hcov
  have hILo : IsILo 2 b J := by
    refine ⟨h.b_ord, ?_, h.comp⟩
    calc oBound 2 = 3 := rfl
      _ ≤ pRank 2 ↥B := hB3
      _ ≤ pRank 2 ↥(centralizer ({b} : Set G)) :=
        C3.Layer1.Back.pRank_mono' (B_le_centralizer h)
  have hKP : IsKProperSimple G := ⟨hyp.simple, hyp.nonab, CFSG.GH74.kProper_of_kgh hyp.kgh⟩
  have hterm : IsTwoTerminal b J :=
    B2.SD.TwoA7TermG.isTwoTerminal_of_twoA7 B2.SD.TwoA7TermG.pumpupTwoA7GH hyp.kgh hKP hILo hbJ
      hcov
  have hZ : center (kBar J) ≠ ⊥ := by
    intro hc
    have h2 := hcov.2.1
    rw [hc, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  exact hyp.noThin ⟨b, J, hterm,
    ⟨hcov.1, Or.inr (Or.inr (Or.inr (Or.inl ⟨7, le_rfl, by norm_num, hcov⟩)))⟩, hZ⟩

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3
