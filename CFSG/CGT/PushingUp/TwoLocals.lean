module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.Defs
import CFSG.GH74.EvenRank
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.CGT.PushingUp

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaximalTwoLocal_ge {L : Subgroup G} (hL : IsPLocal 2 L) :
    ∃ M : Subgroup G, L ≤ M ∧ IsMaximalTwoLocal M := by
  obtain ⟨M, ⟨hM, hLM⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | IsPLocal 2 K ∧ L ≤ K} (fun K => Nat.card K) (Set.toFinite _)
    ⟨L, hL, le_rfl⟩
  refine ⟨M, hLM, hM, fun H hMH hH => ?_⟩
  exact hMH.ne (Subgroup.eq_of_le_of_card_ge hMH.le (hmax H ⟨hH, hLM.trans hMH.le⟩))

omit [Finite G] in
private theorem isPLocal_map_conj {K : Subgroup G} (hK : IsPLocal 2 K) (g : G) :
    IsPLocal 2 (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hK
  refine ⟨P.map (MulAut.conj g).toMonoidHom, fun h => hP1 ?_, hP2.map _,
    Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)⟩
  exact (Subgroup.map_eq_bot_iff_of_injective P (MulAut.conj g).injective).mp h

omit [Finite G] in
theorem isMaximalTwoLocal_map_conj {H : Subgroup G} (hH : IsMaximalTwoLocal H) (g : G) :
    IsMaximalTwoLocal (H.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isPLocal_map_conj hH.1 g, fun K hK hKloc => ?_⟩
  refine hH.2 (K.map (MulAut.conj g⁻¹).toMonoidHom) ?_ (isPLocal_map_conj hKloc g⁻¹)
  have e : (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa [mul_assoc] using ha
    · intro hx
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩
  rw [← e]
  refine lt_of_le_of_ne (Subgroup.map_mono hK.le) fun h => hK.ne ?_
  exact Subgroup.map_injective (MulAut.conj g⁻¹).injective h

omit [Finite G] in
theorem isPLocal_normalizer_of_isPGroup {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    IsPLocal 2 (Subgroup.normalizer (R : Set G)) :=
  ⟨R, hR1, hR, rfl⟩

omit [Finite G] in
private theorem le_pCore_two {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N ≤ pCore 2 G :=
  le_sSup ⟨hN, hp⟩

omit [Finite G] in
theorem pCore_ne_bot_of_isPLocal {H : Subgroup G} (hH : IsPLocal 2 H) : pCore 2 ↥H ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hH
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  have hle : P.subgroupOf (Subgroup.normalizer (P : Set G)) ≤
      pCore 2 ↥(Subgroup.normalizer (P : Set G)) :=
    le_pCore_two Subgroup.normal_in_normalizer hP2.comap_subtype
  intro hbot
  apply hP1
  rw [hbot, le_bot_iff] at hle
  rw [← Subgroup.map_subgroupOf_eq_of_le hPN, hle, Subgroup.map_bot]

omit [Finite G] in
theorem isCharacteristicP_of_isPLocal (hG : CFSG.Assembly.IsCharTwoType G) {H : Subgroup G}
    (hH : IsPLocal 2 H) : IsCharacteristicP 2 ↥H :=
  CFSG.GH74.isCharTwoType_iff.mp hG H hH

theorem pCore_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    pCore 2 G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 G) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup G) := by
      have := pCore_isPGroup (p := 2) (G := G)
      rwa [h] at this
    have hp' : IsPGroup 2 G := hp.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent G := hp'.isNilpotent
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)

theorem ne_top_of_isPLocal [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G}
    (hH : IsPLocal 2 H) : H ≠ ⊤ := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hH
  intro htop
  have hle := le_pCore_two (Subgroup.normalizer_eq_top_iff.mp htop) hP2
  rw [pCore_eq_bot_of_isSimpleGroup hnab, le_bot_iff] at hle
  exact hP1 hle

theorem exists_conj_le_of_isPGroup {M : Subgroup G} (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hRM : R ≤ M) :
    ∃ m ∈ M, R.map (MulAut.conj m).toMonoidHom ≤ (T : Subgroup G) := by
  have hRp : IsPGroup 2 (R.subgroupOf M) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
  obtain ⟨S, hS⟩ := hRp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M (T.subtype hTM) S
  refine ⟨(h : G)⁻¹, (h⁻¹).2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (⟨x, hRM hx⟩ : M) ∈ (S : Subgroup M) := hS hx
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Sylow.coe_subtype,
    Subgroup.mem_subgroupOf] at hxS
  convert hxS using 1
  simp [MulAut.inv_def, MulAut.conj_symm_apply]

private theorem mem_normalizer_of_conj_le {R : Subgroup G} {c : G}
    (h : ∀ r ∈ R, c * r * c⁻¹ ∈ R) : c ∈ Subgroup.normalizer (R : Set G) := by
  have hle : R.map (MulAut.conj c).toMonoidHom ≤ R := by
    rintro _ ⟨r, hr, rfl⟩
    exact h r hr
  have heq : R.map (MulAut.conj c).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hmem : c * x * c⁻¹ ∈ R.map (MulAut.conj c).toMonoidHom := by
    rw [heq]
    exact hx
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyx' : c * y * c⁻¹ = c * x * c⁻¹ := hyx
  exact mul_left_cancel (mul_right_cancel hyx') ▸ hy

private theorem exists_sylow_eq_of_normalizer_le {R D : Subgroup G} (hR : IsPGroup 2 R)
    (hND : Subgroup.normalizer (R : Set G) ≤ D)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ D → R ≤ Q → Q ≤ R) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = R := by
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  refine ⟨T, le_antisymm ?_ hRT⟩
  by_contra hle
  have hnil : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
  have hproper : R.subgroupOf (T : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hle ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥(T : Subgroup G)) ∈ R.subgroupOf (T : Subgroup G) := by
      rw [h]
      trivial
    exact this
  obtain ⟨x, hx_norm, hx_not⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥(T : Subgroup G)) _ hproper)
  have hxN : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have : x ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (T : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq hRT]
      exact hx_norm
    exact this
  have hP₁T : R ⊔ Subgroup.zpowers (x : G) ≤ T := sup_le hRT (Subgroup.zpowers_le.mpr x.2)
  have hP₁2 : IsPGroup 2 (R ⊔ Subgroup.zpowers (x : G) : Subgroup G) :=
    T.isPGroup'.to_le hP₁T
  have hP₁N : R ⊔ Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
  have hxR := hmax _ hP₁2 (hP₁N.trans hND) le_sup_left
  exact hx_not (hxR (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))

theorem isStronglyEmbeddedOrder_of_forall_normalizer_le {M : Subgroup G} (hM : M ≠ ⊤)
    (hev : Even (Nat.card M))
    (h : ∀ R : Subgroup G, R ≠ ⊥ → IsPGroup 2 R → R ≤ M → Subgroup.normalizer (R : Set G) ≤ M) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨hM, hev, fun g hg => ?_⟩
  by_contra hodd
  set D : Subgroup G := M ⊓ M.map (MulAut.conj g).toMonoidHom
  have hDeven : 2 ∣ Nat.card D := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hDeven
  have hZ : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨R₀, hR₀⟩ := hZ.exists_le_sylow
  set R : Subgroup G := (R₀ : Subgroup D).map D.subtype
  have hRD : R ≤ D := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := R₀.isPGroup'.map _
  have hxR : (x : G) ∈ R := ⟨x, hR₀ (Subgroup.mem_zpowers x), rfl⟩
  have hR1 : R ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hxR
    have : x = 1 := Subtype.ext hxR
    rw [this, orderOf_one] at hx
    omega
  have hRmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ D → R ≤ Q → Q ≤ R := by
    intro Q hQ hQD hRQ q hq
    have hQ' : IsPGroup 2 (Q.subgroupOf D) :=
      hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm
    have hle : (R₀ : Subgroup D) ≤ Q.subgroupOf D := fun y hy => hRQ ⟨y, hy, rfl⟩
    have heq := R₀.is_maximal' hQ' hle
    have hq' : (⟨q, hQD hq⟩ : D) ∈ Q.subgroupOf D := hq
    rw [heq] at hq'
    exact ⟨_, hq', rfl⟩
  have hRg : ∀ r ∈ R, g⁻¹ * r * g ∈ M := by
    intro r hr
    obtain ⟨m, hm, hmr⟩ := (hRD hr).2
    have hmr' : g * m * g⁻¹ = r := hmr
    rw [← hmr']
    simpa [mul_assoc] using hm
  have hconj : ∀ r : G, (MulAut.conj g⁻¹).toMonoidHom r = g⁻¹ * r * g := fun r => by
    simp
  set R' : Subgroup G := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hR'M : R' ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hconj]
    exact hRg r hr
  have hR'2 : IsPGroup 2 R' := hR2.map _
  have hR'1 : R' ≠ ⊥ := fun hb =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj g⁻¹).injective).mp hb)
  have hNM : Subgroup.normalizer (R : Set G) ≤ M := h R hR1 hR2 (hRD.trans inf_le_left)
  have hNM' : Subgroup.normalizer (R' : Set G) ≤ M := h R' hR'1 hR'2 hR'M
  have hND : Subgroup.normalizer (R : Set G) ≤ D := by
    refine le_inf hNM fun n hn => ?_
    have hn' : (MulAut.conj g⁻¹).toMonoidHom n ∈ Subgroup.normalizer (R' : Set G) := by
      rw [hR', ← Subgroup.map_equiv_normalizer_eq R (MulAut.conj g⁻¹)]
      exact ⟨n, hn, rfl⟩
    refine ⟨g⁻¹ * n * g, (hconj n) ▸ hNM' hn', ?_⟩
    show g * (g⁻¹ * n * g) * g⁻¹ = n
    group
  obtain ⟨T, hTR⟩ := exists_sylow_eq_of_normalizer_le hR2 hND hRmax
  have hTM : (T : Subgroup G) ≤ M := hTR ▸ hRD.trans inf_le_left
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isPGroup T hTM hR'2 hR'M
  have hc : m * g⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
    refine mem_normalizer_of_conj_le fun r hr => ?_
    have h1 : m * (g⁻¹ * r * g) * m⁻¹ ∈ (T : Subgroup G) :=
      hm ⟨g⁻¹ * r * g, ⟨r, hr, hconj r⟩, rfl⟩
    rw [hTR] at h1
    have e : m * g⁻¹ * r * (m * g⁻¹)⁻¹ = m * (g⁻¹ * r * g) * m⁻¹ := by group
    rwa [e]
  apply hg
  have hgM : g⁻¹ ∈ M := by
    have := M.mul_mem (M.inv_mem hmM) (hNM hc)
    simpa using this
  simpa using M.inv_mem hgM

end CFSG.CGT.PushingUp
