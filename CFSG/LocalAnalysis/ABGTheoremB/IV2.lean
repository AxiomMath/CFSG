module

public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id H]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_oddCoreIn_le [Finite G] (H : Subgroup G) (g : G) :
    (oddCoreIn H).map (MulAut.conj g).toMonoidHom ≤
      oddCoreIn (H.map (MulAut.conj g).toMonoidHom) := by
  apply le_oddCoreIn (Subgroup.map_mono (oddCoreIn_le H))
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (le_normalizer_oddCoreIn H)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact odd_card_oddCoreIn H

private theorem oddCoreIn_map_conj [Finite G] (H : Subgroup G) (g : G) :
    oddCoreIn (H.map (MulAut.conj g).toMonoidHom) =
      (oddCoreIn H).map (MulAut.conj g).toMonoidHom := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (map_conj_oddCoreIn_le H g)
  have h := map_conj_oddCoreIn_le (H.map (MulAut.conj g).toMonoidHom) g⁻¹
  rw [map_conj_inv_map_conj] at h
  calc Nat.card (oddCoreIn (H.map (MulAut.conj g).toMonoidHom))
      = Nat.card ((oddCoreIn (H.map (MulAut.conj g).toMonoidHom)).map
          (MulAut.conj g⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
    _ ≤ Nat.card (oddCoreIn H) := Subgroup.card_le_of_le h
    _ = Nat.card ((oddCoreIn H).map (MulAut.conj g).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

private theorem normalizer_le_normalizer_oddCoreIn [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe] at hg ⊢
  rw [← oddCoreIn_map_conj, hg]

private theorem isSylowOf_map_mulEquiv [Finite G] {r : ℕ} [Fact r.Prime] {P K : Subgroup G}
    (h : IsSylowOf r P K) (e : G ≃* G) :
    IsSylowOf r (P.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  apply isSylowOf_of_card (Subgroup.map_mono h.le)
  rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_map_of_injective e.injective]
  exact h.card_eq

private theorem exists_conj_eq_of_isSylowOf [Finite G] {r : ℕ} [Fact r.Prime]
    {P Q K : Subgroup G} (hP : IsSylowOf r P K) (hQ : IsSylowOf r Q K) :
    ∃ g ∈ K, P.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P' Q'
  refine ⟨g, g.2, ?_⟩
  have hsmul : ((g • P' : Sylow r K) : Subgroup K) =
      (P' : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hg, hsmul, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem exists_isSylowOf_ge [Finite G] {r : ℕ} [Fact r.Prime] {Q K : Subgroup G}
    (hQK : Q ≤ K) (hQ : IsPGroup r Q) : ∃ P : Subgroup G, IsSylowOf r P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
  exact Subgroup.map_mono hS

private theorem lt_inf_normalizer_of_lt [Finite G] {r : ℕ} [Fact r.Prime] {R₀ R : Subgroup G}
    (hR : IsPGroup r R) (hlt : R₀ < R) : R₀ < R ⊓ Subgroup.normalizer (R₀ : Set G) := by
  have hle : R₀ ≤ R := hlt.le
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hlt' : R₀.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hlt.ne
    apply le_antisymm hle
    intro y hy
    have : (⟨y, hy⟩ : R) ∈ R₀.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt'
  rw [← Subgroup.subgroupOf_normalizer_eq hle] at hnorm
  obtain ⟨⟨n, hnR⟩, hnN, hnF⟩ := IsConcreteLE.exists_of_lt hnorm
  refine lt_of_le_of_ne (le_inf hle Subgroup.le_normalizer) fun heq => hnF ?_
  have : n ∈ R ⊓ Subgroup.normalizer (R₀ : Set G) := ⟨hnR, hnN⟩
  rw [← heq] at this
  exact this

private theorem eq_one_of_mul_self_eq_one_of_odd {K : Subgroup G} (hK : Odd (Nat.card K))
    {u : G} (hu : u ∈ K) (h : u * u = 1) : u = 1 := by
  have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h2 : Odd (orderOf u) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hu)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at h2
    exact absurd h2 (by decide)

private theorem conj_mul_inv_mem_of_sup_eq {H K : Subgroup G} {x : G} (hxH : x ∈ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hsup : K ⊔ (H ⊓ Subgroup.centralizer ({x} : Set G)) = H) {h : G} (hh : h ∈ H) :
    x * h * x⁻¹ * h⁻¹ ∈ K := by
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hHK hxH
  let M : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ x * g * x⁻¹ * g⁻¹ ∈ K}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have hconj : a * (x * b * x⁻¹ * b⁻¹) * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp ha _).mp hb'
        have := K.mul_mem ha' hconj
        convert this using 1
        group
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have hconj : a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) _).mp (K.inv_mem ha')
        convert hconj using 1
        group }
  have hKM : K ⊔ (H ⊓ Subgroup.centralizer ({x} : Set G)) ≤ M := by
    refine sup_le (fun k hk => ⟨Subgroup.le_normalizer hk, ?_⟩) (fun c hc => ⟨hHK hc.1, ?_⟩)
    · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxK k).mp hk) (K.inv_mem hk)
    · have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      have : x * c * x⁻¹ * c⁻¹ = 1 := by
        rw [← hcx]
        group
      rw [this]
      exact K.one_mem
  rw [hsup] at hKM
  exact (hKM hh).2

private theorem exists_of_three_dvd_automizerIndex {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer T)
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem three_dvd_automizerIndex_of {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    {g : K}
    (hg : g ∈ Subgroup.normalizer (T : Set K)) (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer T)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h3
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  have := orderOf_dvd_natCard ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt)
  rw [hord, ← Subgroup.index_eq_card] at this
  exact this

private theorem mem_normalizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem exists_of_three_dvd_automizerIndex_subgroupOf [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex h
  refine ⟨g, g.2, (mem_normalizer_subgroupOf_iff hTH).mp hgN, ?_, ?_⟩
  · simpa using (mem_centralizer_subgroupOf_iff hTH).mp hg3
  · exact fun h' => hg1 ((mem_centralizer_subgroupOf_iff hTH).mpr h')

private theorem three_dvd_automizerIndex_subgroupOf_of [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G)) (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  three_dvd_automizerIndex_of (g := ⟨g, hgH⟩) ((mem_normalizer_subgroupOf_iff hTH).mpr hg)
    ((mem_centralizer_subgroupOf_iff hTH).mpr (by simpa using h3))
    (fun h' => h1 ((mem_centralizer_subgroupOf_iff hTH).mp h'))

private theorem le_normalizer_of_conj_mem {A X : Subgroup G}
    (h : ∀ a ∈ A, ∀ y ∈ X, a * y * a⁻¹ ∈ X) : A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h a ha y, fun hy => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

private theorem map_conj_mul_eq (X : Subgroup G) (a b : G) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem le_normalizer_map_conj {A X : Subgroup G} {h : G}
    (hA : h ∈ Subgroup.normalizer (A : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    A ≤ Subgroup.normalizer (X.map (MulAut.conj h).toMonoidHom : Set G) := by
  intro t ht
  have ht' : h⁻¹ * t * h ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hA) t).mp ht
    simpa using this
  have hX := hAX ht'
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe] at hX ⊢
  rw [← map_conj_mul_eq, show t * h = h * (h⁻¹ * t * h) by group, map_conj_mul_eq, hX]

private theorem conj_mem_centralizer_of_mem_normalizer {X : Subgroup G} {g a : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (ha : a ∈ Subgroup.centralizer (X : Set G)) :
    g * a * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
    simpa using this
  have h := (Subgroup.mem_centralizer_iff.mp ha) _ hy'
  calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * a * g⁻¹ * y := by group

private theorem mul_pow_mul_inv_mem {M : Subgroup G} {c g : G} (hc : c ∈ M)
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (n : ℕ) : (c * g) ^ n * (g ^ n)⁻¹ ∈ M := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgn : g ^ n * c * (g ^ n)⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hg n) c).mp hc
    have := M.mul_mem ih hgn
    convert this using 1
    rw [pow_succ, pow_succ]
    group

private def extCentralizer (R : Subgroup G) : Subgroup G where
  carrier := {g | (∀ y ∈ R, g * y * g⁻¹ = y) ∨ (∀ y ∈ R, g * y * g⁻¹ = y⁻¹)}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · left
      intro y hy
      rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group, hb y hy, ha y hy]
    · right
      intro y hy
      rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group, hb y hy,
        ha _ (R.inv_mem hy)]
    · right
      intro y hy
      rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group, hb y hy, ha y hy]
    · left
      intro y hy
      rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group, hb y hy,
        ha _ (R.inv_mem hy), inv_inv]
  one_mem' := Or.inl fun y _ => by group
  inv_mem' := by
    rintro a (ha | ha)
    · left
      intro y hy
      have h := ha y hy
      calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (a * y * a⁻¹) * a := by rw [h, inv_inv]
        _ = y := by group
    · right
      intro y hy
      have h := ha _ (R.inv_mem hy)
      rw [inv_inv] at h
      calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * (a * y⁻¹ * a⁻¹) * a := by rw [h, inv_inv]
        _ = y⁻¹ := by group

private theorem mem_extCentralizer {R : Subgroup G} {g : G} :
    g ∈ extCentralizer R ↔ (∀ y ∈ R, g * y * g⁻¹ = y) ∨ (∀ y ∈ R, g * y * g⁻¹ = y⁻¹) :=
  Iff.rfl

private theorem normalizer_le_normalizer_extCentralizer (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (extCentralizer R : Set G) := by
  refine le_normalizer_of_conj_mem fun m hm g hg => ?_
  have hconj : ∀ y ∈ R, m⁻¹ * y * m ∈ R := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) y).mp hy
    simpa using this
  rcases (mem_extCentralizer.mp hg) with hg | hg
  · left
    intro y hy
    calc m * g * m⁻¹ * y * (m * g * m⁻¹)⁻¹ = m * (g * (m⁻¹ * y * m) * g⁻¹) * m⁻¹ := by group
      _ = y := by rw [hg _ (hconj y hy)]; group
  · right
    intro y hy
    calc m * g * m⁻¹ * y * (m * g * m⁻¹)⁻¹ = m * (g * (m⁻¹ * y * m) * g⁻¹) * m⁻¹ := by group
      _ = y⁻¹ := by rw [hg _ (hconj y hy)]; group

private theorem oddCoreIn_inf_normalizer_le [Finite G] {r : ℕ} [Fact r.Prime]
    {C P : Subgroup G} (hP : IsSylowOf r P (oddCoreIn C)) :
    oddCoreIn (C ⊓ Subgroup.normalizer (P : Set G)) ≤ oddCoreIn C := by
  set M : Subgroup G := oddCoreIn (C ⊓ Subgroup.normalizer (P : Set G)) with hMdef
  have hMC : M ≤ C := (oddCoreIn_le _).trans inf_le_left
  have hYC : oddCoreIn C ⊔ M ≤ C := sup_le (oddCoreIn_le C) hMC
  have hnorm : C ≤ Subgroup.normalizer ((oddCoreIn C ⊔ M : Subgroup G) : Set G) := by
    intro c hc
    have hOeq : (oddCoreIn C).map (MulAut.conj c).toMonoidHom = oddCoreIn C := by
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_oddCoreIn C hc)
      rwa [← MulEquiv.toMonoidHom_eq_coe] at this
    have hPc : IsSylowOf r (P.map (MulAut.conj c).toMonoidHom) (oddCoreIn C) := by
      have := isSylowOf_map_mulEquiv hP (MulAut.conj c)
      rwa [hOeq] at this
    obtain ⟨o, ho, hoc⟩ := exists_conj_eq_of_isSylowOf hPc hP
    have hocN : o * c ∈ C ⊓ Subgroup.normalizer (P : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨C.mul_mem (oddCoreIn_le C ho) hc, ?_⟩
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
        map_conj_mul_eq, hoc]
    have h1 : o * c ∈ Subgroup.normalizer ((oddCoreIn C ⊔ M : Subgroup G) : Set G) :=
      normalizer_inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
        ⟨le_normalizer_oddCoreIn C (Subgroup.mem_inf.mp hocN).1,
          le_normalizer_oddCoreIn _ hocN⟩)
    have h2 : o⁻¹ ∈ Subgroup.normalizer ((oddCoreIn C ⊔ M : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_sup_left ((oddCoreIn C).inv_mem ho))
    simpa using Subgroup.mul_mem _ h2 h1
  have hodd : Odd (Nat.card (oddCoreIn C ⊔ M : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd (hMC.trans (le_normalizer_oddCoreIn C))
      (odd_card_oddCoreIn C) (odd_card_oddCoreIn _)
  exact le_sup_right.trans (le_oddCoreIn hYC hnorm hodd)

private theorem odd_card_of_isPGroup [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hX : IsPGroup r X) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem eq_one_of_mem_of_mem_odd {A K : Subgroup G} (hA : IsPGroup 2 A)
    (hK : Odd (Nat.card K)) {g : G} (hgA : g ∈ A) (hgK : g ∈ K) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨g, hgA⟩
  rw [Subgroup.orderOf_mk] at hk
  have hodd : Odd (orderOf g) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hgK)
  rw [hk] at hodd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))

private theorem exists_mul_self_ne_one_SL2 {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) F, m * m ≠ 1 := by
  let m : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨m, fun h => h2 ?_⟩
  have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have hm : ((m * m : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] * !![1, 1; 0, 1] := rfl
  simp only [hm, Matrix.SpecialLinearGroup.coe_one] at h01
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  rw [← one_add_one_eq_two]
  exact h01

private theorem two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hq := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card] at hq
  obtain ⟨k, hk⟩ := hF
  rw [hk] at hq
  push_cast at hq
  rw [h2, zero_mul, zero_add] at hq
  exact one_ne_zero hq

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

omit [Finite G] in
theorem x_mem_centralizer_ON : σ.x ∈ Subgroup.centralizer (σ.ON : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (σ.mem_N_iff y).mp (σ.ON_le_N hy)

omit [Finite G] in
theorem x_mem_centralizer_of_le_ON {X : Subgroup G} (hX : X ≤ σ.ON) :
    σ.x ∈ Subgroup.centralizer (X : Set G) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX) σ.x_mem_centralizer_ON

omit [Finite G] in
theorem x_mem_normalizer_of_le_ON {X : Subgroup G} (hX : X ≤ σ.ON) :
    σ.x ∈ Subgroup.normalizer (X : Set G) :=
  Subgroup.centralizer_le_normalizer _ (σ.x_mem_centralizer_of_le_ON hX)

omit [Finite G] in
private theorem le_N_of_le_ON {X : Subgroup G} (hX : X ≤ σ.ON) : X ≤ σ.N :=
  hX.trans σ.ON_le_N

omit [Finite G] in
private theorem isPGroup_two_of_le_S {A : Subgroup G} (hA : A ≤ (σ.S : Subgroup G)) :
    IsPGroup 2 A :=
  σ.S.isPGroup'.to_le hA

private theorem isPGroup_two_zpowers_x (hσ : σ.IsValid) :
    IsPGroup 2 (Subgroup.zpowers σ.x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ.x_order, pow_one])

private theorem T_le_normalizer_ON (hσ : σ.IsValid) :
    σ.T ≤ Subgroup.normalizer (σ.ON : Set G) :=
  (σ.T_le_N hσ).trans σ.N_le_normalizer_ON

private theorem x_mul_x (hσ : σ.IsValid) : σ.x * σ.x = 1 := by
  rw [← pow_two, ← hσ.x_order]
  exact pow_orderOf_eq_one _

private theorem x₂_mul_x₂ (hσ : σ.IsValid) : σ.x₂ * σ.x₂ = 1 := by
  rw [← pow_two, ← hσ.x₂_order]
  exact pow_orderOf_eq_one _

private theorem x_inv (hσ : σ.IsValid) : σ.x⁻¹ = σ.x :=
  inv_eq_of_mul_eq_one_right (σ.x_mul_x hσ)

private theorem x₂_inv (hσ : σ.IsValid) : σ.x₂⁻¹ = σ.x₂ :=
  inv_eq_of_mul_eq_one_right (σ.x₂_mul_x₂ hσ)

omit [Finite G] in
theorem T_le_iff {H : Subgroup G} : σ.T ≤ H ↔ σ.x ∈ H ∧ σ.x₂ ∈ H := by
  rw [T, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

omit [Finite G] in
theorem mem_centralizer_T_iff {g : G} :
    g ∈ Subgroup.centralizer (σ.T : Set G) ↔ σ.x * g = g * σ.x ∧ σ.x₂ * g = g * σ.x₂ := by
  rw [T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  simp

theorem mem_T_cases (hσ : σ.IsValid) {t : G} (ht : t ∈ σ.T) :
    t = 1 ∨ t = σ.x ∨ t = σ.x₂ ∨ t = σ.x * σ.x₂ := by
  have hc : Commute σ.x σ.x₂ := hσ.commute
  have key : ∃ a b : ℕ, t = σ.x ^ a * σ.x₂ ^ b := by
    refine Subgroup.closure_induction (p := fun t _ => ∃ a b : ℕ, t = σ.x ^ a * σ.x₂ ^ b)
      ?_ ?_ ?_ ?_ ht
    · rintro g (rfl | rfl)
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    · exact ⟨0, 0, by simp⟩
    · rintro g h _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
      refine ⟨a + c, b + d, ?_⟩
      have hbc : σ.x₂ ^ b * σ.x ^ c = σ.x ^ c * σ.x₂ ^ b := (hc.symm.pow_pow b c).eq
      rw [pow_add, pow_add]
      calc σ.x ^ a * σ.x₂ ^ b * (σ.x ^ c * σ.x₂ ^ d)
          = σ.x ^ a * (σ.x₂ ^ b * σ.x ^ c) * σ.x₂ ^ d := by simp only [mul_assoc]
        _ = σ.x ^ a * (σ.x ^ c * σ.x₂ ^ b) * σ.x₂ ^ d := by rw [hbc]
        _ = σ.x ^ a * σ.x ^ c * (σ.x₂ ^ b * σ.x₂ ^ d) := by simp only [mul_assoc]
    · rintro g _ ⟨a, b, rfl⟩
      refine ⟨a, b, ?_⟩
      rw [mul_inv_rev, ← inv_pow, ← inv_pow, σ.x_inv hσ, σ.x₂_inv hσ]
      exact (hc.symm.pow_pow b a).eq
  obtain ⟨a, b, rfl⟩ := key
  rw [← pow_mod_orderOf σ.x a, hσ.x_order, ← pow_mod_orderOf σ.x₂ b, hσ.x₂_order]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]

private theorem x_ne_one (hσ : σ.IsValid) : σ.x ≠ 1 := by
  intro h
  have h2 := hσ.x_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem x₂_ne_one (hσ : σ.IsValid) : σ.x₂ ≠ 1 := by
  intro h
  have h2 := hσ.x₂_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem conj_x_ne_of_automizer (hσ : σ.IsValid) {g : G}
    (hg : g ∈ Subgroup.normalizer (σ.T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (σ.T : Set G))
    (h1 : g ∉ Subgroup.centralizer (σ.T : Set G)) : g * σ.x * g⁻¹ ≠ σ.x := by
  intro hx
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b h => by
    simpa using h
  have hyT : g * σ.x₂ * g⁻¹ ∈ σ.T := (Subgroup.mem_normalizer_iff.mp hg σ.x₂).mp σ.x₂_mem_T
  have hxx := σ.x_mul_x hσ
  rcases σ.mem_T_cases hσ hyT with hy | hy | hy | hy
  · exact σ.x₂_ne_one hσ (hinj _ _ (by rw [hy]; group))
  · exact hσ.x_ne_x₂ (hinj _ _ (by rw [hy, hx])).symm
  · apply h1
    rw [mem_centralizer_T_iff]
    constructor
    · calc σ.x * g = g * σ.x * g⁻¹ * g := by rw [hx]
        _ = g * σ.x := by group
    · calc σ.x₂ * g = g * σ.x₂ * g⁻¹ * g := by rw [hy]
        _ = g * σ.x₂ := by group
  · have e2 : g * (σ.x * σ.x₂) * g⁻¹ = σ.x₂ := by
      calc g * (σ.x * σ.x₂) * g⁻¹ = (g * σ.x * g⁻¹) * (g * σ.x₂ * g⁻¹) := by group
        _ = σ.x₂ := by rw [hx, hy, ← mul_assoc, hxx, one_mul]
    rw [pow_three'] at h3
    have e3 : g * g * g * σ.x₂ * (g * g * g)⁻¹ = σ.x * σ.x₂ := by
      calc g * g * g * σ.x₂ * (g * g * g)⁻¹ = g * (g * (g * σ.x₂ * g⁻¹) * g⁻¹) * g⁻¹ := by
            group
        _ = σ.x * σ.x₂ := by rw [hy, e2, hy]
    have e4 : g * g * g * σ.x₂ * (g * g * g)⁻¹ = σ.x₂ := by
      have := (Subgroup.mem_centralizer_iff.mp h3) σ.x₂ σ.x₂_mem_T
      rw [← this]
      group
    apply σ.x_ne_one hσ
    have h := e3.symm.trans e4
    simpa using h

theorem x₂_not_mem_solvRad (hσ : σ.IsValid) (hII : σ.NStructure) :
    σ.x₂ ∉ solvRadIn σ.N := by
  rw [hII.N_solvRad, sup_comm]
  intro hmem
  have hZN : centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN] at hmem
  obtain ⟨a, ha, k, hk, hak⟩ := hmem
  beta_reduce at hak
  have hZ2 : IsPGroup 2 (centerOf (σ.S : Subgroup G)) := σ.isPGroup_two_of_le_S inf_le_left
  have hkON : k ∈ σ.ON := hk
  have hx22 := σ.x₂_mul_x₂ hσ
  rw [← hak] at hx22
  have ha2 : a * a = 1 := by
    have hmemON : a * k⁻¹ * a⁻¹ * k⁻¹ ∈ σ.ON :=
      σ.ON.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZN ha) _).mp (σ.ON.inv_mem hkON))
        (σ.ON.inv_mem hkON)
    have e : a = k⁻¹ * a⁻¹ * k⁻¹ := by
      calc a = k⁻¹ * a⁻¹ * (a * k * (a * k)) * k⁻¹ := by group
        _ = k⁻¹ * a⁻¹ * k⁻¹ := by rw [hx22]; group
    have e' : a * a = a * k⁻¹ * a⁻¹ * k⁻¹ := by
      calc a * a = a * (k⁻¹ * a⁻¹ * k⁻¹) := by rw [← e]
        _ = a * k⁻¹ * a⁻¹ * k⁻¹ := by simp only [mul_assoc]
    exact eq_one_of_mem_of_mem_odd hZ2 σ.odd_card_ON
      ((centerOf (σ.S : Subgroup G)).mul_mem ha ha) (e' ▸ hmemON)
  by_cases ha1 : a = 1
  · rw [ha1, one_mul] at hak
    have h1 : σ.x₂ = 1 := eq_one_of_mul_self_eq_one_of_odd σ.odd_card_ON (hak ▸ hkON)
      (σ.x₂_mul_x₂ hσ)
    have h2 := hσ.x₂_order
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    have hax : a = σ.x := hσ.center_involution a ha hao
    rw [hax] at hak
    have hk' : k = σ.x * σ.x₂ := by
      rw [← hak, ← mul_assoc, σ.x_mul_x hσ, one_mul]
    have hkk : k * k = 1 := by
      rw [hk']
      calc σ.x * σ.x₂ * (σ.x * σ.x₂) = σ.x * (σ.x₂ * σ.x) * σ.x₂ := by simp only [mul_assoc]
        _ = σ.x * (σ.x * σ.x₂) * σ.x₂ := by rw [hσ.commute]
        _ = 1 := by rw [← mul_assoc, σ.x_mul_x hσ, one_mul, σ.x₂_mul_x₂ hσ]
    have hk1 : k = 1 := eq_one_of_mul_self_eq_one_of_odd σ.odd_card_ON hkON hkk
    rw [hk1, mul_one] at hak
    exact hσ.x_ne_x₂ hak

omit [Finite G] in
private theorem N_le_normalizer_solvRad :
    σ.N ≤ Subgroup.normalizer (solvRadIn σ.N : Set G) := by
  have : (CFSG.solvableRadical σ.N).Normal := solvableRadical_normal
  exact CFSG.ABGTheoremB.le_normalizer_map_subtype σ.N (CFSG.solvableRadical σ.N)

private theorem ON_le_solvRad (hII : σ.NStructure) : σ.ON ≤ solvRadIn σ.N := by
  rw [hII.N_solvRad]
  exact le_sup_left

private theorem centerOf_S_le_normalizer_ON (hσ : σ.IsValid) :
    centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
  (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON

theorem centralizer_le_solvRad_of_constrained (hσ : σ.IsValid) (hII : σ.NStructure) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hcon : σ.Constrained r) : σ.N ⊓ Subgroup.centralizer (R : Set G) ≤ solvRadIn σ.N := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hW, hPC⟩ := hcon
  set W : Subgroup G := (CFSG.Op_p'p r σ.N).map σ.N.subtype with hWdef
  set Z : Subgroup G := centerOf (σ.S : Subgroup G) with hZdef
  have hWS : W ≤ solvRadIn σ.N := Subgroup.map_mono hW
  have hWN : W ≤ σ.N := Subgroup.map_subtype_le _
  have hNW : σ.N ≤ Subgroup.normalizer (W : Set G) :=
    CFSG.ABGTheoremB.le_normalizer_map_subtype σ.N _
  have hWON : W ≤ Subgroup.normalizer (σ.ON : Set G) := hWN.trans σ.N_le_normalizer_ON
  have hZON : Z ≤ Subgroup.normalizer (σ.ON : Set G) := σ.centerOf_S_le_normalizer_ON hσ
  have hRW : IsSylowOf r (R ⊓ W) W := by
    have hK : IsSylowOf r (R ⊓ (W ⊓ σ.ON)) (W ⊓ σ.ON) :=
      hR.inf_of_le_normalizer inf_le_right
        ((le_inf (σ.ON_le_N.trans hNW) Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    have hRWeq : R ⊓ (W ⊓ σ.ON) = R ⊓ W :=
      le_antisymm (inf_le_inf_left _ inf_le_left)
        (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hR.le)))
    rw [hRWeq] at hK
    rw [isSylowOf_iff]
    refine ⟨inf_le_right, hR.isPGroup.to_le inf_le_left, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex (R ⊓ W) (W ⊓ σ.ON) W
      (le_inf inf_le_right (inf_le_left.trans hR.le)) inf_le_left]
    refine hr.not_dvd_mul (isSylowOf_iff.mp hK).2.2 ?_
    rw [Subgroup.inf_relIndex_left, ← relIndex_sup_right_of_le_normalizer hWON]
    have hdvd : σ.ON.relIndex (W ⊔ σ.ON) ∣ σ.ON.relIndex (Z ⊔ σ.ON) := by
      have hWZ : W ⊔ σ.ON ≤ Z ⊔ σ.ON := by
        rw [sup_le_iff]
        refine ⟨?_, le_sup_right⟩
        have := hWS
        rwa [hII.N_solvRad, sup_comm] at this
      exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hWZ)
    rw [relIndex_sup_right_of_le_normalizer hZON] at hdvd
    have hZ2 : IsPGroup 2 Z := σ.isPGroup_two_of_le_S inf_le_left
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    intro hrd
    have h1 : r ∣ 2 ^ k := hk ▸ hrd.trans (hdvd.trans (Subgroup.relIndex_dvd_card _ _))
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
  have hP : IsSylowOf r ((R ⊓ W).subgroupOf σ.N) (CFSG.Op_p'p r σ.N) := by
    rw [← isSylowOf_map_subtype_iff σ.N, Subgroup.map_subgroupOf_eq_of_le
      (inf_le_right.trans hWN)]
    exact hRW
  intro y hy
  have hyc : (⟨y, hy.1⟩ : σ.N) ∈
      Subgroup.centralizer (((R ⊓ W).subgroupOf σ.N : Subgroup σ.N) : Set σ.N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hy.2) z (Subgroup.mem_subgroupOf.mp hz).1
  exact ⟨⟨y, hy.1⟩, hW (hPC _ hP hyc), rfl⟩

theorem constrained_of_centralizer_le (hσ : σ.IsValid) (hII : σ.NStructure) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hC : σ.N ⊓ Subgroup.centralizer (R : Set G) ≤ solvRadIn σ.N) : σ.Constrained r := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R', hR', hSR'⟩ := exists_isSylowOf_normalized_of_odd hr σ.S.isPGroup'
    ((σ.S_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  obtain ⟨g, hgO, hgR⟩ := exists_conj_eq_of_isSylowOf hR hR'
  have hgN : g ∈ σ.N := σ.ON_le_N hgO
  have hC' : σ.N ⊓ Subgroup.centralizer (R' : Set G) ≤ solvRadIn σ.N := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ σ.N ⊓ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨σ.N.mul_mem (σ.N.mul_mem (σ.N.inv_mem hgN) hy.1) hgN, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : g * z * g⁻¹ ∈ R' := by
        rw [← hgR]
        exact ⟨z, hz, rfl⟩
      have := (Subgroup.mem_centralizer_iff.mp hy.2) _ hz'
      calc z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [this]
        _ = g⁻¹ * y * g * z := by group
    have h2 := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_solvRad hgN) _).mp (hC hy')
    simpa [mul_assoc] using h2
  rw [hII.N_constraint_criterion r hr hdiv R' hR' hSR']
  set Z : Subgroup G := centerOf (σ.S : Subgroup G) with hZdef
  have hZ2 : IsPGroup 2 Z := σ.isPGroup_two_of_le_S inf_le_left
  have hZON : Z ≤ Subgroup.normalizer (σ.ON : Set G) := σ.centerOf_S_le_normalizer_ON hσ
  have hZR' : Z ≤ Subgroup.normalizer (R' : Set G) := inf_le_left.trans hSR'
  have hZ0 : Z ⊓ Subgroup.centralizer (R' : Set G) ≤ σ.N ⊓ Subgroup.centralizer (R' : Set G) :=
    inf_le_inf_right _ (inf_le_left.trans (σ.S_le_N hσ))
  obtain ⟨Q, hQ, hZQ⟩ := exists_isSylowOf_ge hZ0 (hZ2.to_le inf_le_left)
  have hZX : IsSylowOf 2 Z (σ.ON ⊔ Z) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hZ2, ?_⟩
    rw [relIndex_sup_eq_relIndex_of_le_normalizer hZON]
    intro h
    exact (Nat.not_even_iff_odd.mpr σ.odd_card_ON)
      (even_iff_two_dvd.mpr (h.trans (Subgroup.relIndex_dvd_card _ _)))
  have hZY : IsSylowOf 2 Z ((σ.ON ⊔ Z) ⊓ Subgroup.normalizer (R' : Set G)) :=
    hZX.of_le (le_inf le_sup_right hZR') inf_le_left
  have hQY : Q ≤ (σ.ON ⊔ Z) ⊓ Subgroup.normalizer (R' : Set G) := by
    refine le_inf ?_ (hQ.le.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
    have := hQ.le.trans hC'
    rwa [hII.N_solvRad] at this
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_ge hQY hQ.isPGroup
  obtain ⟨h, hhY, hh⟩ := exists_conj_eq_of_isSylowOf hQ' hZY
  have hmap : Q.map (MulAut.conj h).toMonoidHom ≤ Z ⊓ Subgroup.centralizer (R' : Set G) := by
    refine le_inf ?_ ?_
    · rw [← hh]
      exact Subgroup.map_mono hQQ'
    · have hcent := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer R' hhY.2)
      rw [← MulEquiv.toMonoidHom_eq_coe] at hcent
      rw [← hcent]
      exact Subgroup.map_mono (hQ.le.trans inf_le_right)
  have hcard : Nat.card Q ≤ Nat.card (Z ⊓ Subgroup.centralizer (R' : Set G) : Subgroup G) :=
    calc Nat.card Q = Nat.card (Q.map (MulAut.conj h).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj h).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hmap
  rw [Subgroup.eq_of_le_of_card_ge hZQ hcard]
  exact hQ

theorem constrained_iff_centralizer_le (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R σ.ON) :
    σ.Constrained r ↔ σ.N ⊓ Subgroup.centralizer (R : Set G) ≤ solvRadIn σ.N :=
  ⟨σ.centralizer_le_solvRad_of_constrained hσ hII.toNStructure hr
      (σ.prime_ne_two_of_dvd_ON hr hdiv) hR,
    σ.constrained_of_centralizer_le hσ hII.toNStructure hr hdiv hR⟩

private theorem odd_q (hσ : σ.IsValid) : Odd σ.q :=
  (hσ.p_prime.eq_two_or_odd'.resolve_left hσ.p_ne_two).pow

private theorem N_le_normalizer_solvRad_sup (hII : σ.NStructure) {r : ℕ} (hr : r.Prime)
    {R : Subgroup G} (hR : IsSylowOf r R σ.ON) {M : Subgroup G}
    (hM : σ.N ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (M : Set G)) :
    σ.N ≤ Subgroup.normalizer ((solvRadIn σ.N ⊔ M : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  intro n hn
  have hON : σ.ON.map (MulAut.conj n).toMonoidHom = σ.ON := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (σ.N_le_normalizer_ON hn)
    rwa [← MulEquiv.toMonoidHom_eq_coe] at this
  have hRn : IsSylowOf r (R.map (MulAut.conj n).toMonoidHom) σ.ON := by
    have := isSylowOf_map_mulEquiv hR (MulAut.conj n)
    rwa [hON] at this
  obtain ⟨a, haO, ha⟩ := exists_conj_eq_of_isSylowOf hRn hR
  have han : a * n ∈ σ.N ⊓ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨σ.N.mul_mem (σ.ON_le_N haO) hn, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    calc R.map (MulAut.conj (a * n)).toMonoidHom
        = (R.map (MulAut.conj n).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
          rw [Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
      _ = R := ha
  have h1 : a * n ∈ Subgroup.normalizer ((solvRadIn σ.N ⊔ M : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup _ _
      (Subgroup.mem_inf.mpr ⟨σ.N_le_normalizer_solvRad han.1, hM han⟩)
  have h2 : a⁻¹ ∈ Subgroup.normalizer ((solvRadIn σ.N ⊔ M : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_sup_left (σ.ON_le_solvRad hII (σ.ON.inv_mem haO)))
  simpa using Subgroup.mul_mem _ h2 h1

theorem not_constrained_iff_covers (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R σ.ON) :
    ¬ σ.Constrained r ↔ (σ.L₀ : Set G) ⊆
      ((σ.N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) * (σ.ON : Set G) := by
  rw [σ.constrained_iff_centralizer_le hσ hII hr hdiv hR]
  constructor
  · intro hnc
    set M : Subgroup G := σ.N ⊓ Subgroup.centralizer (R : Set G) with hMdef
    have hM : σ.N ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (M : Set G) :=
      (le_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer R))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hK := σ.N_le_normalizer_solvRad_sup hII.toNStructure hr hR hM
    have hKN : solvRadIn σ.N ⊔ M ≤ σ.N := sup_le (solvRadIn_le σ.N) inf_le_left
    have hnot : ¬ solvRadIn σ.N ⊔ M ≤ solvRadIn σ.N := fun h => hnc (le_sup_right.trans h)
    have hL := hII.N_minimalNormal _ hKN hK hnot
    have hL' : σ.L₀ ≤ M ⊔ solvRadIn σ.N :=
      hL.trans (sup_le (sup_le le_sup_right le_sup_left) le_sup_right)
    exact hII.N_coverTransfer M inf_le_left hL'
  · intro hcov hC
    have hL : σ.L₀ ≤ solvRadIn σ.N := by
      intro l hl
      obtain ⟨a, ha, b, hb, hab⟩ := hcov hl
      beta_reduce at hab
      rw [← hab]
      exact (solvRadIn σ.N).mul_mem (hC ha) (σ.ON_le_solvRad hII.toNStructure hb)
    have hLO := hII.N_coverTransfer ⊥ bot_le (hL.trans le_sup_right)
    obtain ⟨F, hFfield, hFfin, hF, ψ, hψ, hker⟩ := hσ.L₀_quotient
    have htriv : ∀ l : σ.L₀, ψ l = 1 := by
      intro l
      have hl : (l : G) ∈ σ.ON := by
        obtain ⟨a, ha, b, hb, hab⟩ := hLO l.2
        beta_reduce at hab
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at ha
        rw [← hab, ha, one_mul]
        exact hb
      have : l ∈ ψ.ker := by
        rw [hker]
        exact hl
      exact MonoidHom.mem_ker.mp this
    obtain ⟨m, hm⟩ := exists_mul_self_ne_one_SL2
      (two_ne_zero_of_odd_card (F := F) (by rw [hF]; exact σ.odd_q hσ))
    obtain ⟨l, rfl⟩ := hψ m
    apply hm
    rw [htriv l, one_mul]

theorem stationary_iff_forall {r : ℕ} (hr : r.Prime) :
    σ.Stationary r ↔ ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      IsSylowOf r R (oddCoreIn (Subgroup.normalizer (R : Set G))) := by
  have : Fact r.Prime := ⟨hr⟩
  constructor
  · rintro ⟨R₀, hR₀, hR₀s⟩ R hR
    obtain ⟨g, -, rfl⟩ := exists_conj_eq_of_isSylowOf hR₀ hR
    have h := isSylowOf_map_mulEquiv hR₀s (MulAut.conj g)
    rwa [← oddCoreIn_map_conj, Subgroup.map_equiv_normalizer_eq] at h
  · intro h
    obtain ⟨R, hR⟩ := exists_isSylowOf r σ.ON
    exact ⟨R, hR, h R hR⟩

theorem exists_T_invariant_sylow (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) :
    ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.T ≤ Subgroup.normalizer (R : Set G) :=
  exists_isSylowOf_normalized_of_odd hr (σ.isPGroup_two_of_le_S (σ.T_le_S hσ))
    (σ.T_le_normalizer_ON hσ) σ.odd_card_ON

theorem exists_D_invariant_sylow (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) :
    ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.D ≤ Subgroup.normalizer (R : Set G) :=
  exists_isSylowOf_normalized_of_odd hr (σ.isPGroup_two_of_le_S σ.D_le_S)
    ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON

theorem centralized_or_inverted_of_T_invariant (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    {R : Subgroup G} (hR : IsSylowOf r R σ.ON) (hTR : σ.T ≤ Subgroup.normalizer (R : Set G)) :
    (σ.Centralized r → σ.T ≤ Subgroup.centralizer (R : Set G)) ∧
      (σ.Inverted r → ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y⁻¹) := by
  have hT2 : IsPGroup 2 σ.T := σ.isPGroup_two_of_le_S (σ.T_le_S hσ)
  have hconj : ∀ R₀ : Subgroup G, IsSylowOf r R₀ σ.ON →
      σ.T ≤ Subgroup.normalizer (R₀ : Set G) →
      ∃ c ∈ σ.ON ⊓ Subgroup.centralizer (σ.T : Set G), R₀.map (MulAut.conj c).toMonoidHom = R :=
    fun R₀ hR₀ hTR₀ => exists_conj_eq_of_isSylowOf_normalized_of_odd hr hT2
      (σ.T_le_normalizer_ON hσ) σ.odd_card_ON hR₀ hR hTR₀ hTR
  constructor
  · rintro ⟨R₀, hR₀, hTR₀, hTC⟩
    obtain ⟨c, hc, rfl⟩ := hconj R₀ hR₀ hTR₀
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have htc : Commute t c := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) t ht
    have hty : y * t = t * y := (Subgroup.mem_centralizer_iff.mp (hTC ht)) y hy
    calc c * y * c⁻¹ * t = c * y * (c⁻¹ * t) := by group
      _ = c * y * (t * c⁻¹) := by rw [htc.inv_right.eq]
      _ = c * (y * t) * c⁻¹ := by group
      _ = c * (t * y) * c⁻¹ := by rw [hty]
      _ = (c * t) * y * c⁻¹ := by group
      _ = (t * c) * y * c⁻¹ := by rw [htc.eq]
      _ = t * (c * y * c⁻¹) := by group
  · rintro ⟨R₀, hR₀, hTR₀, hinv⟩
    obtain ⟨c, hc, rfl⟩ := hconj R₀ hR₀ hTR₀
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : σ.x₂ * c = c * σ.x₂ :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) σ.x₂ σ.x₂_mem_T)
    calc σ.x₂ * (c * y * c⁻¹) * σ.x₂⁻¹ = (σ.x₂ * c) * y * (σ.x₂ * c)⁻¹ := by group
      _ = (c * σ.x₂) * y * (c * σ.x₂)⁻¹ := by rw [e]
      _ = c * (σ.x₂ * y * σ.x₂⁻¹) * c⁻¹ := by group
      _ = c * y⁻¹ * c⁻¹ := by rw [hinv y hy]
      _ = (c * y * c⁻¹)⁻¹ := by group

private theorem conj_x_eq_of_factor (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) {H : Subgroup G}
    (hxH : σ.x ∈ H) (hfac : oddCoreIn H ⊔ (H ⊓ σ.N) = H)
    (hsyl : ∀ P : Subgroup G, IsSylowOf r P (oddCoreIn H) →
      σ.x ∈ Subgroup.normalizer (P : Set G) → σ.x ∈ Subgroup.centralizer (P : Set G))
    {X : Subgroup G} (hX : IsPGroup r X) {y : G} (hyH : y ∈ H) (hyX : y ∈ X)
    (hxyX : σ.x * y * σ.x⁻¹ ∈ X) : σ.x * y * σ.x⁻¹ = y := by
  have : Fact r.Prime := ⟨hr⟩
  set d := σ.x * y * σ.x⁻¹ * y⁻¹ with hd
  have hdO : d ∈ oddCoreIn H :=
    conj_mul_inv_mem_of_sup_eq hxH (le_normalizer_oddCoreIn H) hfac hyH
  have hdX : d ∈ X := X.mul_mem hxyX (X.inv_mem hyX)
  have hxx := σ.x_mul_x hσ
  have hxinv := σ.x_inv hσ
  have hdinv : σ.x * d * σ.x⁻¹ = d⁻¹ := by
    rw [hd, hxinv]
    calc σ.x * (σ.x * y * σ.x * y⁻¹) * σ.x = (σ.x * σ.x) * y * σ.x * y⁻¹ * σ.x := by group
      _ = y * σ.x * y⁻¹ * σ.x := by rw [hxx, one_mul]
      _ = (σ.x * y * σ.x * y⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, hxinv, mul_assoc]
  have hZ : IsPGroup r (Subgroup.zpowers d) := hX.to_le (Subgroup.zpowers_le.mpr hdX)
  have hZO : Subgroup.zpowers d ≤ oddCoreIn H := Subgroup.zpowers_le.mpr hdO
  have hxZ : σ.x ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have : (MulAut.conj σ.x : G →* G) d = d⁻¹ := by
      rw [MonoidHom.coe_ofClass, MulAut.conj_apply, hdinv]
    rw [this, Subgroup.zpowers_inv]
  obtain ⟨P, hP, hZP, hAP⟩ := exists_isSylowOf_normalized_ge_of_odd hr
    (σ.isPGroup_two_zpowers_x hσ) (Subgroup.zpowers_le.mpr (le_normalizer_oddCoreIn H hxH))
    (odd_card_oddCoreIn H) hZO hZ (Subgroup.zpowers_le.mpr hxZ)
  have hxP := hsyl P hP (hAP (Subgroup.mem_zpowers σ.x))
  have hcomm : d * σ.x = σ.x * d :=
    (Subgroup.mem_centralizer_iff.mp hxP) d (hZP (Subgroup.mem_zpowers d))
  have hdd : d * d = 1 := by
    have h1 : σ.x * d * σ.x⁻¹ = d := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hdinv] at h1
    calc d * d = d⁻¹ * d := by rw [h1]
      _ = 1 := inv_mul_cancel d
  have hd1 : d = 1 := eq_one_of_mul_self_eq_one_of_odd (odd_card_oddCoreIn H) hdO hdd
  rw [hd] at hd1
  exact mul_inv_eq_one.mp hd1

private theorem forall_centralized_of_exists (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    {K : Subgroup G} (hxK : σ.x ∈ Subgroup.normalizer (K : Set G)) (hK : Odd (Nat.card K))
    (h : ∃ P₀ : Subgroup G, IsSylowOf r P₀ K ∧ σ.x ∈ Subgroup.centralizer (P₀ : Set G)) :
    ∀ P : Subgroup G, IsSylowOf r P K → σ.x ∈ Subgroup.normalizer (P : Set G) →
      σ.x ∈ Subgroup.centralizer (P : Set G) := by
  obtain ⟨P₀, hP₀, hxP₀⟩ := h
  intro P hP hxP
  obtain ⟨c, hc, rfl⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr
    (σ.isPGroup_two_zpowers_x hσ) (Subgroup.zpowers_le.mpr hxK) hK hP₀ hP
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hxP₀))
    (Subgroup.zpowers_le.mpr hxP)
  have hxc : σ.x * c = c * σ.x :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) σ.x (Subgroup.mem_zpowers _)
  have hcx : Commute σ.x c := hxc
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hyx : y * σ.x = σ.x * y := (Subgroup.mem_centralizer_iff.mp hxP₀) y hy
  calc c * y * c⁻¹ * σ.x = c * y * (c⁻¹ * σ.x) := by group
    _ = c * y * (σ.x * c⁻¹) := by rw [hcx.inv_right.eq]
    _ = c * (y * σ.x) * c⁻¹ := by group
    _ = c * (σ.x * y) * c⁻¹ := by rw [hyx]
    _ = (c * σ.x) * y * c⁻¹ := by group
    _ = (σ.x * c) * y * c⁻¹ := by rw [hxc]
    _ = σ.x * (c * y * c⁻¹) := by group

private theorem exists_sylow_centralized_aux (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hstat : ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      IsSylowOf r R (oddCoreIn (Subgroup.normalizer (R : Set G))))
    (hcov : ∀ R : Subgroup G, IsSylowOf r R σ.ON → (σ.L₀ : Set G) ⊆
      ((σ.N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) * (σ.ON : Set G)) :
    ∀ n : ℕ, ∀ R₀ : Subgroup G, Nat.card σ.ON - Nat.card R₀ = n → R₀ ≠ ⊥ → IsPGroup r R₀ →
      R₀ ≤ σ.ON → σ.T ≤ Subgroup.normalizer (R₀ : Set G) →
      ∃ P : Subgroup G, IsSylowOf r P (oddCoreIn (Subgroup.normalizer (R₀ : Set G))) ∧
        σ.x ∈ Subgroup.centralizer (P : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R₀ hn hR₀ hR₀p hR₀O hTR₀
  obtain ⟨R, hR, hR₀R, hTR⟩ := exists_isSylowOf_normalized_ge_of_odd hr
    (σ.isPGroup_two_of_le_S (σ.T_le_S hσ)) (σ.T_le_normalizer_ON hσ) σ.odd_card_ON hR₀O hR₀p
    hTR₀
  by_cases hEq : R₀ = R
  · subst hEq
    exact ⟨R₀, hstat R₀ hR, σ.x_mem_centralizer_of_le_ON hR₀O⟩
  have hlt : R₀ < R := lt_of_le_of_ne hR₀R hEq
  set R₁ : Subgroup G := R ⊓ Subgroup.normalizer (R₀ : Set G) with hR₁def
  have hR₀R₁ : R₀ < R₁ := lt_inf_normalizer_of_lt hR.isPGroup hlt
  have hR₁O : R₁ ≤ σ.ON := inf_le_left.trans hR.le
  have hR₁p : IsPGroup r R₁ := hR.isPGroup.to_le inf_le_left
  have hR₁ : R₁ ≠ ⊥ := fun h => hR₀ (le_bot_iff.mp (h ▸ hR₀R₁.le))
  have hTR₁ : σ.T ≤ Subgroup.normalizer (R₁ : Set G) :=
    (le_inf hTR (hTR₀.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hcard : Nat.card σ.ON - Nat.card R₁ < n := by
    have h1 := Subgroup.card_lt_of_lt hR₀R₁
    have h2 := Subgroup.card_le_of_le hR₁O
    omega
  obtain ⟨P₁, hP₁, hxP₁⟩ := ih _ hcard R₁ rfl hR₁ hR₁p hR₁O hTR₁
  set H₁ : Subgroup G := Subgroup.normalizer (R₁ : Set G) with hH₁def
  have hxH₁ : σ.x ∈ H₁ := σ.x_mem_normalizer_of_le_ON hR₁O
  have hsyl₁ := σ.forall_centralized_of_exists hσ hr (le_normalizer_oddCoreIn H₁ hxH₁)
    (odd_card_oddCoreIn H₁) ⟨P₁, hP₁, hxP₁⟩
  have hO₁ : oddCoreIn H₁ ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 ⟨R₁, hR₁, hR₁p, rfl⟩
  have hcov₁ : (σ.L₀ : Set G) ⊆ (H₁ : Set G) * (σ.ON : Set G) := by
    refine (hcov R hR).trans (Set.mul_subset_mul_right ?_)
    intro c hc
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr inf_le_left) (Subgroup.mem_inf.mp hc).2)
  have hfac₁ := (hII.cover_qgroup H₁ hTR₁ hO₁ hcov₁).2
  by_contra hno
  set H₀ : Subgroup G := Subgroup.normalizer (R₀ : Set G) with hH₀def
  have hxH₀ : σ.x ∈ H₀ := σ.x_mem_normalizer_of_le_ON hR₀O
  have hR₁N : R₁ ≤ Subgroup.normalizer (oddCoreIn H₀ : Set G) :=
    (inf_le_right : R₁ ≤ H₀).trans (le_normalizer_oddCoreIn H₀)
  have hYodd : Odd (Nat.card (oddCoreIn H₀ ⊔ R₁ : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hR₁N (odd_card_oddCoreIn H₀)
      (odd_card_of_isPGroup hr hr2 hR₁p)
  have hAY : Subgroup.zpowers σ.x ≤
      Subgroup.normalizer ((oddCoreIn H₀ ⊔ R₁ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_inf_normalizer_le_normalizer_sup _ _
      (Subgroup.mem_inf.mpr ⟨le_normalizer_oddCoreIn H₀ hxH₀, hxH₁⟩))
  obtain ⟨R₂, hR₂, hR₁R₂, hAR₂⟩ := exists_isSylowOf_normalized_ge_of_odd hr
    (σ.isPGroup_two_zpowers_x hσ) hAY hYodd le_sup_right hR₁p (Subgroup.zpowers_le.mpr hxH₁)
  have hR₂O := hR₂.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hR₁N)
  have hxnot : σ.x ∉ Subgroup.centralizer ((R₂ ⊓ oddCoreIn H₀ : Subgroup G) : Set G) :=
    fun h => hno ⟨_, hR₂O, h⟩
  have hxR₂ : σ.x ∈ Subgroup.normalizer (R₂ : Set G) := hAR₂ (Subgroup.mem_zpowers _)
  have hlt₂ : R₂ ⊓ Subgroup.centralizer ({σ.x} : Set G) < R₂ := by
    refine lt_of_le_of_ne inf_le_left fun heq => hxnot ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y ∈ R₂ ⊓ Subgroup.centralizer ({σ.x} : Set G) := by
      rw [heq]
      exact (Subgroup.mem_inf.mp hy).1
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp this).2
  have hR₂odd := odd_card_of_isPGroup hr hr2 hR₂.isPGroup
  obtain ⟨u, hu, hu1, huc⟩ := exists_inverted_centralizing_fixed hR₂.isPGroup hR₂odd
    hσ.x_order hxR₂ hlt₂
  obtain ⟨huR₂, hux⟩ := OddInversion.mem_invertedSet.mp hu
  have hR₁C : R₁ ≤ R₂ ⊓ Subgroup.centralizer ({σ.x} : Set G) :=
    le_inf hR₁R₂ (σ.le_N_of_le_ON hR₁O)
  have huH₁ : u ∈ H₁ := Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₁C) huc)
  have hxu := σ.conj_x_eq_of_factor hσ hr hxH₁ hfac₁ hsyl₁ hR₂.isPGroup huH₁ huR₂
    (by rw [hux]; exact R₂.inv_mem huR₂)
  rw [hux] at hxu
  apply hu1
  apply eq_one_of_mul_self_eq_one_of_odd hR₂odd huR₂
  calc u * u = u⁻¹ * u := by rw [hxu]
    _ = 1 := inv_mul_cancel u

theorem x_centralizes_local_sylow (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) (hstat : σ.Stationary r)
    (hnc : ¬ σ.Constrained r) {R₀ : Subgroup G} (hR₀ : R₀ ≠ ⊥) (hR₀p : IsPGroup r R₀)
    (hR₀O : R₀ ≤ σ.ON) (hTR₀ : σ.T ≤ Subgroup.normalizer (R₀ : Set G)) :
    (∀ P : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf r P (oddCoreIn (Subgroup.normalizer (R₀ : Set G))) →
        σ.x ∈ Subgroup.normalizer (P : Set G) → σ.x ∈ Subgroup.centralizer (P : Set G)) ∧
      ∃ P : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf r P (oddCoreIn (Subgroup.normalizer (R₀ : Set G))) ∧
          σ.x ∈ Subgroup.centralizer (P : Set G) := by
  have hr2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hex := σ.exists_sylow_centralized_aux hσ hII hr hr2 ((σ.stationary_iff_forall hr).mp hstat)
    (fun R hR => (σ.not_constrained_iff_covers hσ hII hr hdiv hR).mp hnc) _ R₀ rfl hR₀ hR₀p
    hR₀O hTR₀
  exact ⟨σ.forall_centralized_of_exists hσ hr
    (le_normalizer_oddCoreIn _ (σ.x_mem_normalizer_of_le_ON hR₀O)) (odd_card_oddCoreIn _) hex,
    hex⟩

private theorem not_L₀_subset_zpowers_x₂_mul (hσ : σ.IsValid) :
    ¬ (σ.L₀ : Set G) ⊆ (Subgroup.zpowers σ.x₂ : Set G) * (σ.ON : Set G) := by
  intro hL
  obtain ⟨F, hFfield, hFfin, hF, ψ, hψ, hker⟩ := hσ.L₀_quotient
  have hsq : ∀ l : σ.L₀, ψ l * ψ l = 1 := by
    intro l
    obtain ⟨g, hg, a, ha, hga⟩ := hL l.2
    beta_reduce at hga
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgg : σ.x₂ ^ k * σ.x₂ ^ k = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, σ.x₂_mul_x₂ hσ, one_zpow]
    have hgN : σ.x₂ ^ k ∈ σ.N := Subgroup.zpow_mem _ (σ.x₂_mem_N hσ) k
    have hll : (l : G) * l ∈ σ.ON := by
      rw [← hga]
      have hconj : σ.x₂ ^ k * a * (σ.x₂ ^ k)⁻¹ ∈ σ.ON :=
        (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON hgN) a).mp ha
      have : σ.x₂ ^ k * a * (σ.x₂ ^ k * a) = σ.x₂ ^ k * a * (σ.x₂ ^ k)⁻¹ * a := by
        rw [show (σ.x₂ ^ k)⁻¹ = σ.x₂ ^ k from inv_eq_of_mul_eq_one_right hgg]
        simp only [mul_assoc]
      rw [this]
      exact σ.ON.mul_mem hconj ha
    have : l * l ∈ ψ.ker := by
      rw [hker]
      exact hll
    rw [← map_mul]
    exact MonoidHom.mem_ker.mp this
  obtain ⟨m, hm⟩ := exists_mul_self_ne_one_SL2
    (two_ne_zero_of_odd_card (F := F) (by rw [hF]; exact σ.odd_q hσ))
  obtain ⟨l, rfl⟩ := hψ m
  exact hm (hsq l)

theorem not_constrained_of_ordinary (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) (hord : σ.Ordinary r) : ¬ σ.Constrained r := by
  intro hcon
  rcases hord.2 with ⟨R, hR, hTR, hTC⟩ | ⟨R, hR, hTR, hinv⟩
  · have hC := (σ.constrained_iff_centralizer_le hσ hII hr hdiv hR).mp hcon
    exact σ.x₂_not_mem_solvRad hσ hII.toNStructure
      (hC (Subgroup.mem_inf.mpr ⟨σ.x₂_mem_N hσ, hTC σ.x₂_mem_T⟩))
  · have hC := (σ.constrained_iff_centralizer_le hσ hII hr hdiv hR).mp hcon
    set K : Subgroup G := σ.N ⊓ extCentralizer R with hKdef
    have hx₂K : σ.x₂ ∈ K :=
      Subgroup.mem_inf.mpr ⟨σ.x₂_mem_N hσ, mem_extCentralizer.mpr (Or.inr hinv)⟩
    have hM : σ.N ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G) :=
      (le_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans (normalizer_le_normalizer_extCentralizer R))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hnorm := σ.N_le_normalizer_solvRad_sup hII.toNStructure hr hR hM
    have hKN : solvRadIn σ.N ⊔ K ≤ σ.N := sup_le (solvRadIn_le σ.N) inf_le_left
    have hnot : ¬ solvRadIn σ.N ⊔ K ≤ solvRadIn σ.N := fun h =>
      σ.x₂_not_mem_solvRad hσ hII.toNStructure (h (Subgroup.mem_sup_right hx₂K))
    have hL := hII.N_minimalNormal _ hKN hnorm hnot
    have hKS : K ≤ Subgroup.zpowers σ.x₂ ⊔ solvRadIn σ.N := by
      intro g hg
      obtain ⟨hgN, hgE⟩ := Subgroup.mem_inf.mp hg
      rcases mem_extCentralizer.mp hgE with hgc | hgi
      · refine Subgroup.mem_sup_right (hC (Subgroup.mem_inf.mpr ⟨hgN, ?_⟩))
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        calc y * g = g * y * g⁻¹ * g := by rw [hgc y hy]
          _ = g * y := by group
      · have hgx : g * σ.x₂ ∈ σ.N ⊓ Subgroup.centralizer (R : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨σ.N.mul_mem hgN (σ.x₂_mem_N hσ), ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have h1 : g * σ.x₂ * y * (g * σ.x₂)⁻¹ = y := by
            calc g * σ.x₂ * y * (g * σ.x₂)⁻¹ = g * (σ.x₂ * y * σ.x₂⁻¹) * g⁻¹ := by group
              _ = y := by rw [hinv y hy, hgi _ (R.inv_mem hy), inv_inv]
          calc y * (g * σ.x₂) = g * σ.x₂ * y * (g * σ.x₂)⁻¹ * (g * σ.x₂) := by rw [h1]
            _ = g * σ.x₂ * y := by group
        have : g = (g * σ.x₂) * σ.x₂⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hC hgx))
          (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
    have hL' : σ.L₀ ≤ Subgroup.zpowers σ.x₂ ⊔ solvRadIn σ.N :=
      hL.trans (sup_le (sup_le le_sup_right hKS) le_sup_right)
    exact σ.not_L₀_subset_zpowers_x₂_mul hσ (hII.N_coverTransfer _
      (Subgroup.zpowers_le.mpr (σ.x₂_mem_N hσ)) hL')

omit [Finite G] in
private theorem D_le_normalizer_C : σ.D ≤ Subgroup.normalizer (σ.C : Set G) :=
  inf_le_right.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer σ.T)

private theorem ON_inf_C_le_oddCoreIn_C : σ.ON ⊓ σ.C ≤ oddCoreIn σ.C :=
  le_oddCoreIn inf_le_right
    ((le_inf (σ.C_le_N.trans σ.N_le_normalizer_ON) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem exists_sylow_C_sylow_ON (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) :
    ∃ P R : Subgroup G, IsSylowOf r P (oddCoreIn σ.C) ∧
      σ.D ≤ Subgroup.normalizer (P : Set G) ∧ IsSylowOf r R σ.ON ∧
      σ.T ≤ Subgroup.normalizer (R : Set G) ∧ P ≤ Subgroup.normalizer (R : Set G) ∧
      IsPGroup r (P ⊔ R : Subgroup G) ∧ ∀ y ∈ R, σ.x₂ * y * σ.x₂⁻¹ = y → y ∈ P := by
  have : Fact r.Prime := ⟨hr⟩
  have hT2 : IsPGroup 2 σ.T := σ.isPGroup_two_of_le_S (σ.T_le_S hσ)
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_normalized_of_odd hr (σ.isPGroup_two_of_le_S σ.D_le_S)
    (σ.D_le_normalizer_C.trans (normalizer_le_normalizer_oddCoreIn σ.C))
    (odd_card_oddCoreIn σ.C)
  have hPC : P ≤ σ.C := hP.le.trans (oddCoreIn_le _)
  have hTPn : σ.T ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp hPC).trans (Subgroup.centralizer_le_normalizer _)
  have hOCON : oddCoreIn σ.C ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (oddCoreIn_le _).trans (σ.C_le_N.trans σ.N_le_normalizer_ON)
  have hYodd : Odd (Nat.card (σ.ON ⊔ oddCoreIn σ.C : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hOCON σ.odd_card_ON (odd_card_oddCoreIn _)
  have hTY : σ.T ≤ Subgroup.normalizer ((σ.ON ⊔ oddCoreIn σ.C : Subgroup G) : Set G) :=
    fun t ht => normalizer_inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
      ⟨σ.T_le_normalizer_ON hσ ht, le_normalizer_oddCoreIn σ.C (σ.T_le_C hσ ht)⟩)
  obtain ⟨Rs, hRs, hPRs, hTRs⟩ := exists_isSylowOf_normalized_ge_of_odd hr hT2 hTY hYodd
    (hP.le.trans le_sup_right) hP.isPGroup hTPn
  have hYN : σ.ON ⊔ oddCoreIn σ.C ≤ Subgroup.normalizer (σ.ON : Set G) :=
    sup_le Subgroup.le_normalizer hOCON
  refine ⟨P, Rs ⊓ σ.ON, hP, hDP, hRs.inf_of_le_normalizer le_sup_left hYN,
    (le_inf hTRs (σ.T_le_normalizer_ON hσ)).trans Subgroup.inf_normalizer_le_normalizer_inf,
    (le_inf (hPRs.trans Subgroup.le_normalizer)
      (hPC.trans (σ.C_le_N.trans σ.N_le_normalizer_ON))).trans
      Subgroup.inf_normalizer_le_normalizer_inf,
    hRs.isPGroup.to_le (sup_le hPRs inf_le_left), ?_⟩
  intro y hy hfix
  obtain ⟨hyRs, hyON⟩ := Subgroup.mem_inf.mp hy
  have hyC : y ∈ σ.C := by
    rw [C, mem_centralizer_T_iff]
    refine ⟨((Subgroup.mem_centralizer_iff.mp σ.x_mem_centralizer_ON) y hyON).symm, ?_⟩
    calc σ.x₂ * y = σ.x₂ * y * σ.x₂⁻¹ * σ.x₂ := by group
      _ = y * σ.x₂ := by rw [hfix]
  have hyOC : y ∈ oddCoreIn σ.C := σ.ON_inf_C_le_oddCoreIn_C (Subgroup.mem_inf.mpr ⟨hyON, hyC⟩)
  have heq : Rs ⊓ oddCoreIn σ.C = P :=
    hP.eq_of_le (le_inf hPRs hP.le) inf_le_right (hRs.isPGroup.to_le inf_le_left)
  rw [← heq]
  exact Subgroup.mem_inf.mpr ⟨hyRs, hyOC⟩

private theorem exists_automizer_three_normalizer (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) {P : Subgroup G} (hP : IsSylowOf r P (oddCoreIn σ.C)) :
    ∃ h ∈ Subgroup.normalizer (σ.T : Set G) ⊓ Subgroup.normalizer (P : Set G),
      h ^ 3 ∈ Subgroup.centralizer (σ.T : Set G) ∧ h ∉ Subgroup.centralizer (σ.T : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨g₀, hg₀N, hg₀3, hg₀1⟩ :=
    exists_of_three_dvd_automizerIndex (T := σ.T) (by rw [hII.automizer_T]; norm_num)
  have hg₀C : g₀ ∈ Subgroup.normalizer (σ.C : Set G) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer σ.T hg₀N
  have hOCeq : (oddCoreIn σ.C).map (MulAut.conj g₀).toMonoidHom = oddCoreIn σ.C := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_oddCoreIn σ.C hg₀C)
    rwa [← MulEquiv.toMonoidHom_eq_coe] at this
  have hPg : IsSylowOf r (P.map (MulAut.conj g₀).toMonoidHom) (oddCoreIn σ.C) := by
    have := isSylowOf_map_mulEquiv hP (MulAut.conj g₀)
    rwa [hOCeq] at this
  obtain ⟨c, hcO, hc⟩ := exists_conj_eq_of_isSylowOf hPg hP
  have hcC : c ∈ Subgroup.centralizer (σ.T : Set G) := oddCoreIn_le _ hcO
  refine ⟨c * g₀, Subgroup.mem_inf.mpr
    ⟨Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hcC) hg₀N, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, map_conj_mul_eq,
      hc]
  · have h1 := mul_pow_mul_inv_mem hcC (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer σ.T hg₀N) 3
    have := Subgroup.mul_mem _ h1 hg₀3
    simpa using this
  · intro h
    exact hg₀1 (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) h)

private theorem isDGroupWrt_normalizer (hII : σ.ChapterIIFacts) {P K : Subgroup G}
    (hDP : σ.D ≤ Subgroup.normalizer (P : Set G)) (hTP : σ.T ≤ Subgroup.centralizer (P : Set G))
    (hQK : IsQGroup K) (hPK : Subgroup.centralizer (P : Set G) ≤ K) {h : G}
    (hh : h ∈ Subgroup.normalizer (σ.T : Set G) ⊓ Subgroup.normalizer (P : Set G))
    (hh3 : h ^ 3 ∈ Subgroup.centralizer (σ.T : Set G))
    (hh1 : h ∉ Subgroup.centralizer (σ.T : Set G)) :
    IsDGroupWrt (σ.T.subgroupOf (Subgroup.normalizer (P : Set G))) ∧
      Group.IsSolvable (Subgroup.normalizer (P : Set G)) := by
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hHdef
  have hTH : σ.T ≤ H := hTP.trans (Subgroup.centralizer_le_normalizer _)
  have h3H := three_dvd_automizerIndex_subgroupOf_of hTH (Subgroup.mem_inf.mp hh).2
    (Subgroup.mem_inf.mp hh).1 hh3 hh1
  have hnot : ¬ (IsQDGroup H ∨ (IsDGroupWrt (σ.T.subgroupOf H) ∧ ¬ Group.IsSolvable H)) := by
    intro hbad
    obtain ⟨T₁, hT₁X, hT₁, h3⟩ := hII.normal_contains_three H hDP hbad
      (Subgroup.centralizer (P : Set G)) (Subgroup.centralizer_le_normalizer _)
      (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer P) hTP
    obtain ⟨g₁, hg₁X, hg₁N, hg₁3, hg₁1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf hT₁X h3
    exact hII.qgroup_no_three K hQK T₁ (hT₁X.trans hPK) hT₁
      (three_dvd_automizerIndex_subgroupOf_of (hT₁X.trans hPK) (hPK hg₁X) hg₁N hg₁3 hg₁1)
  rcases hII.qd_or_d_of_three H hTH (Or.inl hDP) h3H with hqd | hdw
  · exact absurd (Or.inl hqd) hnot
  · refine ⟨hdw, ?_⟩
    by_contra hns
    exact hnot (Or.inr ⟨hdw, hns⟩)

theorem centralized_or_inverted_of_stationary (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) (hstat : σ.Stationary r)
    (hnc : ¬ σ.Constrained r) : σ.Centralized r ∨ σ.Inverted r := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hT2 : IsPGroup 2 σ.T := σ.isPGroup_two_of_le_S (σ.T_le_S hσ)
  obtain ⟨P, R, hP, hDP, hR, hTR, hPR, hPRp, hfix⟩ := σ.exists_sylow_C_sylow_ON hσ hr
  have hPC : P ≤ σ.C := hP.le.trans (oddCoreIn_le _)
  have hTP : σ.T ≤ Subgroup.centralizer (P : Set G) := Subgroup.le_centralizer_iff.mp hPC
  by_cases hbot : P ⊓ R = ⊥
  ·
    right
    refine ⟨R, hR, hTR, ?_⟩
    have hRodd : Odd (Nat.card R) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hR.le)
    have hdec := (odd_fixed_mul_inverted hRodd hσ.x₂_order (hTR σ.x₂_mem_T)).1
    have hF : R ⊓ Subgroup.centralizer ({σ.x₂} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hyR, hyc⟩ := Subgroup.mem_inf.mp hy
      have hyc' : σ.x₂ * y * σ.x₂⁻¹ = y := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hyc]
        group
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hfix y hyR hyc', hyR⟩
    intro y hy
    have hy' : y ∈ (R : Set G) := hy
    rw [hdec, hF] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    beta_reduce at hab
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at ha
    rw [← hab, ha, one_mul]
    exact (OddInversion.mem_invertedSet.mp hb).2
  by_cases hRP : R ≤ P
  · left
    exact ⟨R, hR, hTR, Subgroup.le_centralizer_iff.mp (hRP.trans hPC)⟩
  exfalso
  set R₀ : Subgroup G := P ⊓ R with hR₀def
  have hR₀O : R₀ ≤ σ.ON := inf_le_right.trans hR.le
  have hR₀p : IsPGroup r R₀ := hR.isPGroup.to_le inf_le_right
  have hTR₀ : σ.T ≤ Subgroup.normalizer (R₀ : Set G) :=
    (le_inf (hTP.trans (Subgroup.centralizer_le_normalizer _)) hTR).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  set K : Subgroup G := Subgroup.normalizer (R₀ : Set G) with hKdef
  have hOK : oddCoreIn K ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 ⟨R₀, hbot, hR₀p, rfl⟩
  have hcovK : (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G) := by
    refine ((σ.not_constrained_iff_covers hσ hII hr hdiv hR).mp hnc).trans
      (Set.mul_subset_mul_right ?_)
    intro c hc
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr inf_le_right) (Subgroup.mem_inf.mp hc).2)
  obtain ⟨hKq, hfacK⟩ := hII.cover_qgroup K hTR₀ hOK hcovK
  have hPK : Subgroup.centralizer (P : Set G) ≤ K :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨h₀, hh₀, hh₀3, hh₀1⟩ := σ.exists_automizer_three_normalizer hII hr hP
  obtain ⟨hHd, hHs⟩ := σ.isDGroupWrt_normalizer hII hDP hTP hKq.1 hPK hh₀ hh₀3 hh₀1
  set H : Subgroup G := Subgroup.normalizer (P : Set G) with hHdef
  have hTH : σ.T ≤ H := hTP.trans (Subgroup.centralizer_le_normalizer _)
  set P₁ : Subgroup G := R ⊓ H with hP₁def
  obtain ⟨y₁, hy₁P₁, hy₁P⟩ : ∃ y ∈ P₁, y ∉ P := by
    have hlt : P < P ⊔ R := lt_of_le_of_ne le_sup_left fun h => hRP (h ▸ le_sup_right)
    obtain ⟨g, hg, hgP⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer_of_lt hPRp hlt)
    obtain ⟨hgQ, hgN⟩ := Subgroup.mem_inf.mp hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPR] at hgQ
    obtain ⟨a, ha, b, hb, hab⟩ := hgQ
    beta_reduce at hab
    refine ⟨b, Subgroup.mem_inf.mpr ⟨hb, ?_⟩, fun hbP => hgP (hab ▸ P.mul_mem ha hbP)⟩
    have : b = a⁻¹ * g := by rw [← hab]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer ha)) hgN
  have hTP₁ : σ.T ≤ Subgroup.normalizer (P₁ : Set G) :=
    (le_inf hTR (hTH.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hP₁p : IsPGroup r P₁ := hR.isPGroup.to_le inf_le_left
  have hP₁O : P₁ ≤ oddCoreIn H :=
    hII.solvable_dgroup_signalizer H hDP hHd hHs r hr hr2 P₁ inf_le_right hP₁p hTP₁
  have hPO : P ≤ oddCoreIn H :=
    le_oddCoreIn Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup hr hr2 hP.isPGroup)
  have hQp : IsPGroup r (P₁ ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hP₁p hP.isPGroup inf_le_right
  have hTQ : σ.T ≤ Subgroup.normalizer ((P₁ ⊔ P : Subgroup G) : Set G) := fun t ht =>
    normalizer_inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr ⟨hTP₁ ht, hTH ht⟩)
  have hTOH : σ.T ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    hTH.trans (le_normalizer_oddCoreIn H)
  obtain ⟨Ps, hPs, hQPs, hTPs⟩ := exists_isSylowOf_normalized_ge_of_odd hr hT2 hTOH
    (odd_card_oddCoreIn H) (sup_le hP₁O hPO) hQp hTQ
  have hPPs : P ≤ Ps := le_sup_right.trans hQPs
  have hPsC : ¬ Ps ≤ σ.C := by
    intro hPsC
    have h1 : Ps ≤ oddCoreIn (σ.C ⊓ H) := by
      refine le_trans (le_inf hPsC hPs.le) (le_oddCoreIn (inf_le_inf_left _ (oddCoreIn_le H))
        ?_ ((odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)))
      exact (le_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans (le_normalizer_oddCoreIn H))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have heq := hP.eq_of_le hPPs (h1.trans (oddCoreIn_inf_normalizer_le hP)) hPs.isPGroup
    exact hy₁P (heq ▸ hQPs (Subgroup.mem_sup_left hy₁P₁))
  have hh₀T : h₀ ∈ Subgroup.normalizer (σ.T : Set G) := (Subgroup.mem_inf.mp hh₀).1
  have hOHeq : (oddCoreIn H).map (MulAut.conj h₀).toMonoidHom = oddCoreIn H := by
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_oddCoreIn H
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh₀).2))
    rwa [← MulEquiv.toMonoidHom_eq_coe] at this
  have hPs' : IsSylowOf r (Ps.map (MulAut.conj h₀).toMonoidHom) (oddCoreIn H) := by
    have := isSylowOf_map_mulEquiv hPs (MulAut.conj h₀)
    rwa [hOHeq] at this
  obtain ⟨c, hc, hcPs⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr hT2 hTOH
    (odd_card_oddCoreIn H) hPs' hPs (le_normalizer_map_conj hh₀T hTPs) hTPs
  have hcT : c ∈ Subgroup.centralizer (σ.T : Set G) := (Subgroup.mem_inf.mp hc).2
  have hhN : c * h₀ ∈ Subgroup.normalizer (σ.T : Set G) :=
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hcT) hh₀T
  have hhPs : c * h₀ ∈ Subgroup.normalizer (Ps : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, map_conj_mul_eq,
      hcPs]
  have hh3 : (c * h₀) ^ 3 ∈ Subgroup.centralizer (σ.T : Set G) := by
    have h1 := mul_pow_mul_inv_mem hcT (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer σ.T hh₀T) 3
    simpa using Subgroup.mul_mem _ h1 hh₀3
  have hh1 : c * h₀ ∉ Subgroup.centralizer (σ.T : Set G) := fun hm =>
    hh₀1 (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hcT) hm)
  have hxPs : σ.x ∉ Subgroup.centralizer (Ps : Set G) := by
    intro hx
    have hne := σ.conj_x_ne_of_automizer hσ hhN hh3 hh1
    have hyT : c * h₀ * σ.x * (c * h₀)⁻¹ ∈ σ.T :=
      (Subgroup.mem_normalizer_iff.mp hhN σ.x).mp σ.x_mem_T
    have hyC := conj_mem_centralizer_of_mem_normalizer hhPs hx
    have hx₂C : σ.x₂ ∈ Subgroup.centralizer (Ps : Set G) := by
      rcases σ.mem_T_cases hσ hyT with h1 | h1 | h1 | h1
      · exfalso
        apply σ.x_ne_one hσ
        have := congrArg (fun z => (c * h₀)⁻¹ * z * (c * h₀)) h1
        simpa [mul_assoc] using this
      · exact absurd h1 hne
      · rwa [h1] at hyC
      · rw [h1] at hyC
        simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hyC
    exact hPsC (Subgroup.le_centralizer_iff.mp (σ.T_le_iff.mpr ⟨hx, hx₂C⟩))
  have hPsodd := odd_card_of_isPGroup hr hr2 hPs.isPGroup
  have hlt : Ps ⊓ Subgroup.centralizer ({σ.x} : Set G) < Ps := by
    refine lt_of_le_of_ne inf_le_left fun heq => hxPs ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y ∈ Ps ⊓ Subgroup.centralizer ({σ.x} : Set G) := by
      rw [heq]
      exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp this).2
  obtain ⟨u, hu, hu1, huc⟩ := exists_inverted_centralizing_fixed hPs.isPGroup hPsodd
    hσ.x_order (hTPs σ.x_mem_T) hlt
  obtain ⟨huPs, hux⟩ := OddInversion.mem_invertedSet.mp hu
  have hR₀C : R₀ ≤ Ps ⊓ Subgroup.centralizer ({σ.x} : Set G) :=
    le_inf (inf_le_left.trans hPPs) (σ.le_N_of_le_ON hR₀O)
  have huK : u ∈ K := Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀C) huc)
  have hsylK := (σ.x_centralizes_local_sylow hσ hII hr hdiv hstat hnc hbot hR₀p hR₀O hTR₀).1
  have hxu := σ.conj_x_eq_of_factor hσ hr (σ.x_mem_normalizer_of_le_ON hR₀O) hfacK hsylK
    hPs.isPGroup huK huPs (by rw [hux]; exact Ps.inv_mem huPs)
  rw [hux] at hxu
  apply hu1
  apply eq_one_of_mul_self_eq_one_of_odd hPsodd huPs
  calc u * u = u⁻¹ * u := by rw [hxu]
    _ = 1 := inv_mul_cancel u

theorem ordinary_iff (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime)
    (hdiv : r ∣ Nat.card σ.ON) :
    σ.Ordinary r ↔ σ.Stationary r ∧ ¬ σ.Constrained r :=
  ⟨fun h => ⟨h.1, σ.not_constrained_of_ordinary hσ hII hr hdiv h⟩,
    fun h => ⟨h.1, σ.centralized_or_inverted_of_stationary hσ hII hr hdiv h.1 h.2⟩⟩

theorem conj_eq_or_eq_inv_of_ordinary (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hord : σ.Ordinary r) {R : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hTR : σ.T ≤ Subgroup.normalizer (R : Set G)) {t : G} (ht : t ∈ σ.T) {u : G} (hu : u ∈ R) :
    t * u * t⁻¹ = u ∨ t * u * t⁻¹ = u⁻¹ := by
  obtain ⟨hcen, hinv⟩ := σ.centralized_or_inverted_of_T_invariant hσ hr hR hTR
  have hxu : σ.x * u * σ.x⁻¹ = u := by
    rw [← (Subgroup.mem_centralizer_iff.mp (σ.x_mem_centralizer_of_le_ON hR.le)) u hu]
    group
  rcases hord.2 with hc | hi
  · left
    rw [← (Subgroup.mem_centralizer_iff.mp (hcen hc ht)) u hu]
    group
  · have hx₂u := hinv hi u hu
    rcases σ.mem_T_cases hσ ht with rfl | rfl | rfl | rfl
    · left
      group
    · exact Or.inl hxu
    · exact Or.inr hx₂u
    · right
      calc σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ = σ.x * (σ.x₂ * u * σ.x₂⁻¹) * σ.x⁻¹ := by group
        _ = (σ.x * u * σ.x⁻¹)⁻¹ := by rw [hx₂u]; group
        _ = u⁻¹ := by rw [hxu]

theorem ordinary_element_centralizer (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON) (hord : σ.Ordinary r) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R σ.ON)
    (hTR : σ.T ≤ Subgroup.normalizer (R : Set G)) {u : G} (hu : u ∈ R) (hu1 : u ≠ 1) :
    σ.T ≤ Subgroup.normalizer (Subgroup.centralizer ({u} : Set G) : Set G) ∧
      ∀ X : Subgroup G, X ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup r X →
        σ.T ≤ Subgroup.normalizer (X : Set G) → X ≤ σ.N := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  set U : Subgroup G := Subgroup.zpowers u with hUdef
  have hcU : Subgroup.centralizer (U : Set G) = Subgroup.centralizer ({u} : Set G) := by
    rw [hUdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hTU : σ.T ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.map_zpowers]
    have e : (MulAut.conj t).toMonoidHom u = t * u * t⁻¹ := rfl
    rw [e]
    rcases σ.conj_eq_or_eq_inv_of_ordinary hσ hr hord hR hTR ht hu with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hTC : σ.T ≤ Subgroup.normalizer (Subgroup.centralizer ({u} : Set G) : Set G) := by
    rw [← hcU]
    exact hTU.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer U)
  refine ⟨hTC, ?_⟩
  intro X hXu hXp hTX
  have hUp : IsPGroup r U := hR.isPGroup.to_le (Subgroup.zpowers_le.mpr hu)
  have hUO : U ≤ σ.ON := Subgroup.zpowers_le.mpr (hR.le hu)
  have hU : U ≠ ⊥ := fun h => hu1 (by
    have : u ∈ U := Subgroup.mem_zpowers u
    rw [h] at this
    exact (Subgroup.mem_bot.mp this))
  set H : Subgroup G := Subgroup.normalizer (U : Set G) with hHdef
  have hCH : Subgroup.centralizer ({u} : Set G) ≤ H := by
    rw [← hcU]
    exact Subgroup.centralizer_le_normalizer _
  have hTH : σ.T ≤ H := hTU
  have hOH : oddCoreIn H ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr hr2 ⟨U, hU, hUp, rfl⟩
  have hnc := ((σ.ordinary_iff hσ hII hr hdiv).mp hord).2
  have hcovH : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) := by
    refine ((σ.not_constrained_iff_covers hσ hII hr hdiv hR).mp hnc).trans
      (Set.mul_subset_mul_right ?_)
    intro c hc
    refine hCH ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) u hu).symm
  have hfac := (hII.cover_qgroup H hTH hOH hcovH).2
  have hsyl := (σ.x_centralizes_local_sylow hσ hII hr hdiv
    ((σ.ordinary_iff hσ hII hr hdiv).mp hord).1 hnc hU hUp hUO hTU).1
  intro y hy
  have hxy := σ.conj_x_eq_of_factor hσ hr (hTH σ.x_mem_T) hfac hsyl hXp (hCH (hXu hy)) hy
    ((Subgroup.mem_normalizer_iff.mp (hTX σ.x_mem_T) y).mp hy)
  rw [mem_N_iff]
  calc y * σ.x = σ.x * y * σ.x⁻¹ * σ.x := by rw [hxy]
    _ = σ.x * y := by group

end Setting

end CFSG.ABGTheoremB
