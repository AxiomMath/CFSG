module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_eq_range_mul_ker {H N : Type*} [Group H] [Finite H] [Group N] (ψ : H →* N) :
    Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker

theorem eq_of_central_aut {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) (α : Q →* Q)
    (h : ∀ q, α q * q⁻¹ ∈ Subgroup.center Q) (q : Q) : α q = q := by
  let c : Q →* Subgroup.center Q :=
    { toFun := fun q => ⟨α q * q⁻¹, h q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q r => Subtype.ext (by
        have hz := Subgroup.mem_center_iff.1 (h r)
        show α (q * r) * (q * r)⁻¹ = (α q * q⁻¹) * (α r * r⁻¹)
        calc α (q * r) * (q * r)⁻¹ = (α q * (α r * r⁻¹)) * q⁻¹ := by
              rw [map_mul, mul_inv_rev]; simp only [mul_assoc]
          _ = ((α r * r⁻¹) * α q) * q⁻¹ := by rw [hz (α q)]
          _ = (α r * r⁻¹) * (α q * q⁻¹) := by group
          _ = (α q * q⁻¹) * (α r * r⁻¹) := (hz (α q * q⁻¹)).symm) }
  have hker : ∀ g r : Q, c ⁅g, r⁆ = 1 := fun g r => by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (c r).2 (c g)))
  have htop : commutator Q ≤ c.ker :=
    Subgroup.commutator_le.2 fun g _ r _ => MonoidHom.mem_ker.2 (hker g r)
  rw [hQ] at htop
  have hq := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top q))
  exact mul_inv_eq_one.1 (congrArg Subtype.val hq)

noncomputable def conjEnd (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    K →* K :=
  (conjL K g⁻¹ (Subgroup.inv_mem _ hg)).toMonoidHom

theorem conjEnd_val (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (q : K) :
    ((conjEnd K g hg q : K) : G) = g * q * g⁻¹ := by
  simp [conjEnd, conjL_apply]

theorem conjEnd_mul (K : Subgroup G) {g h : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hh : h ∈ Subgroup.normalizer (K : Set G)) (q : K) :
    conjEnd K (g * h) (mul_mem hg hh) q = conjEnd K g hg (conjEnd K h hh q) :=
  Subtype.ext (by rw [conjEnd_val, conjEnd_val, conjEnd_val]; group)

end Generic

variable {G : Type} [Group G] [Finite G]

theorem eq_of_conj_eq' {K : Subgroup G} {ε : K →* A8} (hε : Function.Surjective ε) {m m' : A8}
    (h : ∀ k : K, m * ε k * m⁻¹ = m' * ε k * m'⁻¹) : m = m' := by
  have hz : m'⁻¹ * m ∈ Subgroup.center A8 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := hε y
    have h2 : m'⁻¹ * (m * ε k * m⁻¹) * m' = ε k := by rw [h k]; group
    calc ε k * (m'⁻¹ * m) = (m'⁻¹ * (m * ε k * m⁻¹) * m') * (m'⁻¹ * m) := by rw [h2]
      _ = (m'⁻¹ * m) * ε k := by group
  rw [a8_center, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

theorem exists_iso_of_pSimple {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (eS : PSimple 3 K ≃* A8) :
    (∃ e : PQuot 3 K ≃* A8, GLAPPrimeCore 3 ↥K = Subgroup.center ↥K) ∧
      Nat.card (Subgroup.center ↥K) ∣ 2 := by
  classical
  have hOne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro h
    have hP : ∀ a b : ↥K, (a : PQuot 3 K) = b := fun a b =>
      QuotientGroup.eq.2 (by rw [h]; exact Subgroup.mem_top _)
    have hS : ∀ z w : PSimple 3 K, z = w := by
      intro z w
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [hP a' b']
    have hA : ∀ x y : A8, x = y := fun x y => eS.symm.injective (hS _ _)
    exact a8c8_ne_one (hA _ _)
  have hOZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hK (GLAPPrimeCore.normal 3 ↥K) hOne
  let m : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)
  let mz : PQuot 3 K →* PSimple 3 K := QuotientGroup.mk' (Subgroup.center (PQuot 3 K))
  let π₀ : ↥K →* A8 := eS.toMonoidHom.comp (mz.comp m)
  have hπs : Function.Surjective π₀ :=
    eS.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hker0 : π₀.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hk1 : mz (m k) = 1 := eS.injective (hk.trans (map_one eS).symm)
      have hcen : m k ∈ Subgroup.center (PQuot 3 K) := (QuotientGroup.eq_one_iff _).1 hk1
      have hcomm' : ∀ q : ↥K, k * q * k⁻¹ * q⁻¹ ∈ GLAPPrimeCore 3 ↥K := by
        intro q
        have h1 : m (k * q * k⁻¹ * q⁻¹) = 1 := by
          have hc := (Subgroup.mem_center_iff.1 hcen (m q)).symm
          simp only [map_mul, map_inv]
          rw [hc]
          group
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hkc : ∀ q : ↥K, conjEnd K (k : G) (Subgroup.le_normalizer k.2) q = q := by
        intro q
        refine eq_of_central_aut hK.1 (conjEnd K (k : G) (Subgroup.le_normalizer k.2)) (fun q => ?_) q
        have heq : conjEnd K (k : G) (Subgroup.le_normalizer k.2) q * q⁻¹ = k * q * k⁻¹ * q⁻¹ :=
          Subtype.ext (by simp [conjEnd_val, mul_assoc])
        rw [heq]
        exact hOZ (hcomm' q)
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg' : (k : G) * g * (k : G)⁻¹ = g := by
        rw [← conjEnd_val K (Subgroup.le_normalizer k.2)]; exact congrArg Subtype.val (hkc g)
      show (g : G) * k = k * g
      calc (g : G) * k = ((k : G) * g * (k : G)⁻¹) * k := by rw [hg']
        _ = k * g := by group
    · intro hz
      have hmz : m k ∈ Subgroup.center (PQuot 3 K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
        show m q * m k = m k * m q
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
      have : mz (m k) = 1 := (QuotientGroup.eq_one_iff _).2 hmz
      show eS (mz (m k)) = 1
      rw [this, map_one]
  have hS := card_center_dvd_hopfMultiplier_of_cover hK π₀ hπs hker0
  rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := 8) (by norm_num)] at hS
  have hZO : Subgroup.center ↥K ≤ GLAPPrimeCore 3 ↥K := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right hS (by norm_num)⟩
  have hO : GLAPPrimeCore 3 ↥K = Subgroup.center ↥K := le_antisymm hOZ hZO
  have hcen : Subgroup.center (PQuot 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : mz (m x) = 1 := (QuotientGroup.eq_one_iff _).2 hy
    have hx : x ∈ Subgroup.center ↥K := by
      rw [← hker0, MonoidHom.mem_ker]
      show eS (mz (m x)) = 1
      rw [h1, map_one]
    have hxO : x ∈ GLAPPrimeCore 3 ↥K := hO ▸ hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).2 hxO
  exact ⟨⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans eS, hO⟩,
    hS⟩

theorem inner_of_pow3 {K : Subgroup G} (e : PQuot 3 K ≃* A8) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ m : A8, ∀ k : ↥K, piOf K e (conjEnd K b hb k) = m * piOf K e k * m⁻¹ := by
  have hb' : b⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hb
  have hα : barAut K b⁻¹ hb' ^ 3 = 1 := barAut_pow_three K b⁻¹ hb' (by rw [inv_pow, hb3, inv_one])
  have hβ : MulAut.congr e (barAut K b⁻¹ hb') ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hne : ¬ 3 ∣ Nat.card (Outer A8) :=
    CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup 8 (by norm_num) 3 Nat.prime_three (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : A8, MulAut.conj m = MulAut.congr e (barAut K b⁻¹ hb') :=
    MonoidHom.mem_range.1 (forall_cube_inner_of_card_outer hne _ hβ)
  refine ⟨m, fun k => ?_⟩
  have h1 : barAut K b⁻¹ hb' (QuotientGroup.mk k) = QuotientGroup.mk (conjEnd K b hb k) :=
    barAut_mk _ _ _ _
  have h2 := congrArg (fun φ : MulAut A8 => φ (e (QuotientGroup.mk k))) hm
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  rw [h1] at h2
  exact h2.symm

theorem exists_rho {K B D : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hDeq : D = B ⊓ Subgroup.centralizer (K : Set G))
    {ε : ↥K →* A8} (hε : Function.Surjective ε) (hεker : ε.ker = Subgroup.center ↥K)
    (hinner : ∀ b : ↥B, ∃ m : A8, ∀ k : ↥K, ε (conjEnd K b.1 (hBN b.2) k) = m * ε k * m⁻¹) :
    ∃ ρ : ↥B →* A8, (∀ (b : ↥B) (k : ↥K), ε (conjEnd K b.1 (hBN b.2) k) = ρ b * ε k * (ρ b)⁻¹) ∧
      ∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ D := by
  choose f hf using hinner
  have hmul : ∀ b c : ↥B, f (b * c) = f b * f c := by
    intro b c
    refine eq_of_conj_eq' hε (fun k => ?_)
    calc f (b * c) * ε k * (f (b * c))⁻¹ = ε (conjEnd K (b * c : ↥B).1 (hBN (b * c).2) k) :=
          (hf _ k).symm
      _ = ε (conjEnd K b.1 (hBN b.2) (conjEnd K c.1 (hBN c.2) k)) :=
          congrArg ε (conjEnd_mul K (hBN b.2) (hBN c.2) k)
      _ = f b * ε (conjEnd K c.1 (hBN c.2) k) * (f b)⁻¹ := hf b _
      _ = f b * (f c * ε k * (f c)⁻¹) * (f b)⁻¹ := by rw [hf c k]
      _ = f b * f c * ε k * (f b * f c)⁻¹ := by group
  refine ⟨MonoidHom.mk' f hmul, fun b k => hf b k, fun b => ⟨fun hb1 => ?_, fun hD => ?_⟩⟩
  · have hb1' : f b = 1 := hb1
    have hcent : ∀ q : ↥K, conjEnd K b.1 (hBN b.2) q = q := by
      intro q
      refine eq_of_central_aut hKq.1 (conjEnd K b.1 (hBN b.2)) (fun q => ?_) q
      rw [← hεker, MonoidHom.mem_ker, map_mul, map_inv, hf b q, hb1']
      simp
    have hcb : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := congrArg Subtype.val (hcent ⟨h, hh⟩)
      rw [conjEnd_val] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hDeq]
    exact ⟨b.2, hcb⟩
  · have hcb : (b : G) ∈ Subgroup.centralizer (K : Set G) := by rw [hDeq] at hD; exact hD.2
    have hcent : ∀ k : ↥K, conjEnd K b.1 (hBN b.2) k = k := fun k => by
      apply Subtype.ext
      rw [conjEnd_val]
      have h' := Subgroup.mem_centralizer_iff.1 hcb k k.2
      calc (b : G) * k * (b : G)⁻¹ = k * b * (b : G)⁻¹ := by rw [← h']
        _ = k := by group
    show f b = 1
    refine eq_of_conj_eq' hε (fun k => ?_)
    rw [← hf b k, hcent k, one_mul, inv_one, mul_one]

open scoped Pointwise in
theorem exists_conj_of_card9 {R : Subgroup A8} (hR : Nat.card R = 9) (hR3 : IsPGroup 3 R) :
    ∃ g : A8, ∀ m : A8, m ∈ a8P0 ↔ g * m * g⁻¹ ∈ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP0 : IsPGroup 3 a8P0 := a8P0_three
  have hsyl : ∀ H : Subgroup A8, IsPGroup 3 H → Nat.card H = 9 →
      ∃ Q : Sylow 3 A8, (Q : Subgroup A8) = H := by
    intro H hH hHc
    obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have hd : 3 ^ n ∣ 20160 := by
      rw [← a8_card, ← hn]; exact Subgroup.card_subgroup_dvd_card _
    have hn2 := a8_three_part_perm n hd
    have hle : Nat.card (Q : Subgroup A8) ≤ Nat.card H := by
      rw [hHc, hn]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hn2) (by norm_num)
    exact ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ hle).symm⟩
  obtain ⟨Q₁, hQ₁⟩ := hsyl R hR3 hR
  obtain ⟨Q₂, hQ₂⟩ := hsyl a8P0 hP0 a8P0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A8 Q₂ Q₁
  refine ⟨g, fun m => ?_⟩
  have hset : ((Q₁ : Subgroup A8) : Set A8) = MulAut.conj g • ((Q₂ : Subgroup A8) : Set A8) := by
    rw [← hg]; exact Sylow.coe_smul
  have h := Set.smul_mem_smul_set_iff (a := MulAut.conj g) (s := ((Q₂ : Subgroup A8) : Set A8))
    (x := m)
  rw [← hset] at h
  rw [← hQ₁, ← hQ₂]
  exact h.symm

theorem subsingleton_quot {H : Type*} [Group H] [Subsingleton H] (N : Subgroup H) :
    Subsingleton (H ⧸ N) :=
  ⟨fun x y => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subsingleton.elim a b]⟩

theorem standardize {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G))
    {ε : ↥K →* A8} (hε : Function.Surjective ε) {ρ : ↥B →* A8}
    (hrel : ∀ (b : ↥B) (k : ↥K), ε (conjEnd K b.1 (hBN b.2) k) = ρ b * ε k * (ρ b)⁻¹)
    (hcard : Nat.card ρ.range = 9) (hR3 : IsPGroup 3 ρ.range) :
    ∃ (ε' : ↥K →* A8) (ρ' : ↥B →* A8), Function.Surjective ε' ∧ ε'.ker = ε.ker ∧
      (∀ (b : ↥B) (k : ↥K), ε' (conjEnd K b.1 (hBN b.2) k) = ρ' b * ε' k * (ρ' b)⁻¹) ∧
      (∀ b : ↥B, ρ' b = 1 ↔ ρ b = 1) ∧ ρ'.range = a8P0 := by
  obtain ⟨g, hg⟩ := exists_conj_of_card9 hcard hR3
  let c : A8 →* A8 := (MulAut.conj g⁻¹).toMonoidHom
  have hc : ∀ x, c x = g⁻¹ * x * g := fun x => by simp [c, MulAut.conj_apply]
  have hc1 : ∀ x : A8, c x = 1 ↔ x = 1 := fun x => by
    rw [hc]
    constructor
    · intro h
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h; rw [h]; group
  refine ⟨c.comp ε, c.comp ρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := hε (g * y * g⁻¹)
    exact ⟨k, by simp only [MonoidHom.comp_apply, hc, hk]; group⟩
  · ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact hc1 _
  · intro b k
    simp only [MonoidHom.comp_apply, hc, hrel b k]
    group
  · intro b
    simp only [MonoidHom.comp_apply]
    exact hc1 _
  · ext m
    constructor
    · rintro ⟨b, rfl⟩
      show c (ρ b) ∈ a8P0
      rw [hg]
      have hm : g * c (ρ b) * g⁻¹ = ρ b := by rw [hc]; group
      rw [hm]
      exact MonoidHom.mem_range.2 ⟨b, rfl⟩
    · intro hm
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 ((hg m).1 hm)
      refine ⟨b, ?_⟩
      show c (ρ b) = m
      rw [hb, hc]
      group

theorem T_part {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G))
    {ε : ↥K →* A8} (hε : Function.Surjective ε) (hεker : ε.ker = Subgroup.center ↥K)
    (hc2 : Nat.card (Subgroup.center ↥K) ∣ 2) (hO : GLAPPrimeCore 3 ↥K = Subgroup.center ↥K)
    {ρ : ↥B →* A8}
    (hrel : ∀ (b : ↥B) (k : ↥K), ε (conjEnd K b.1 (hBN b.2) k) = ρ b * ε k * (ρ b)⁻¹)
    (hρr : ρ.range = a8P0) (b₁ : ↥B) (hb₁ : ρ b₁ = a8c8) :
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ 8 < Nat.card T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K := by
  set T₀ : Subgroup ↥K := a8V0.comap ε with hT₀
  have hcenT : Subgroup.center ↥K ≤ T₀ := fun z hz => by
    have h1 : ε z = 1 := MonoidHom.mem_ker.1 (by rw [hεker]; exact hz)
    show ε z ∈ a8V0
    rw [h1]; exact one_mem _
  have hr : (ε.comp T₀.subtype).range = a8V0 := by
    ext v
    constructor
    · rintro ⟨t, rfl⟩; exact t.2
    · intro hv
      obtain ⟨k, rfl⟩ := hε v
      exact ⟨⟨k, hv⟩, rfl⟩
  have hk : (ε.comp T₀.subtype).ker = (Subgroup.center ↥K).subgroupOf T₀ := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hεker, MonoidHom.mem_ker]
    rfl
  have hcard : Nat.card T₀ = Nat.card a8V0 * Nat.card (Subgroup.center ↥K) := by
    have h1 := card_eq_range_mul_ker (ε.comp T₀.subtype)
    rw [hr, hk] at h1
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenT).toEquiv]
  obtain ⟨kV, hkV⟩ := a8V0_two.exists_card_eq
  have hT2 : IsPGroup 2 ↥T₀ := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hc2 with h | h
    · exact IsPGroup.of_card (n := kV) (by rw [hcard, hkV, h, mul_one])
    · exact IsPGroup.of_card (n := kV + 1) (by rw [hcard, hkV, h, pow_succ])
  have hTc : Nat.card (T₀.map K.subtype) = Nat.card T₀ :=
    (Nat.card_congr (Subgroup.equivMapOfInjective T₀ K.subtype K.subtype_injective).toEquiv).symm
  have hTmem : ∀ x : G, x ∈ T₀.map K.subtype ↔ ∃ t : ↥K, t ∈ T₀ ∧ (t : G) = x := fun x => by
    constructor
    · intro hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_map.2 ⟨t, ht, rfl⟩
  have hnorm : ∀ b ∈ B, ∀ x ∈ T₀.map K.subtype, b * x * b⁻¹ ∈ T₀.map K.subtype := by
    intro b hb x hx
    obtain ⟨t, ht, rfl⟩ := (hTmem x).1 hx
    rw [hTmem]
    refine ⟨conjEnd K b (hBN hb) t, ?_, conjEnd_val K _ t⟩
    show ε (conjEnd K b (hBN hb) t) ∈ a8V0
    rw [hrel ⟨b, hb⟩ t]
    have hρmem : ρ ⟨b, hb⟩ ∈ a8P0 := by
      rw [← hρr]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
    exact a8_normalizes hρmem ht
  have hBN' : B ≤ Subgroup.normalizer ((T₀.map K.subtype : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hnorm b hb x
    · intro hx
      simpa [mul_assoc] using hnorm b⁻¹ (inv_mem hb) _ hx
  have hcomm_ne : (⁅T₀.map K.subtype, B⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    obtain ⟨y₀, hy₀⟩ := hε a8v1
    have hy₀T : (y₀ : G) ∈ T₀.map K.subtype :=
      (hTmem _).2 ⟨y₀, show ε y₀ ∈ a8V0 by rw [hy₀]; exact a8v1_mem_V0, rfl⟩
    have hcm := Subgroup.commutator_mem_commutator hy₀T (b₁.2 : b₁.1 ∈ B)
    rw [hbot, Subgroup.mem_bot] at hcm
    have hcom : (b₁ : G) * y₀ = y₀ * b₁ := (commutatorElement_eq_one_iff_mul_comm.1 hcm).symm
    have hfix : conjEnd K b₁.1 (hBN b₁.2) y₀ = y₀ := Subtype.ext (by
      rw [conjEnd_val, hcom]; group)
    have h1 := hrel b₁ y₀
    rw [hfix, hy₀, hb₁] at h1
    exact a8_nontriv h1.symm
  have hbig : 8 < Nat.card (T₀.map K.subtype) := by
    rw [hTc, hcard]
    have h1 := Nat.card_pos (α := ↥(Subgroup.center ↥K))
    have h2 : Nat.card a8V0 ≤ Nat.card a8V0 * Nat.card (Subgroup.center ↥K) :=
      Nat.le_mul_of_pos_right _ h1
    have h9 := a8V0_big
    omega
  have hnotle : ¬ T₀.map K.subtype ≤ GLAPPrimeCoreOf 3 K := by
    intro hle
    obtain ⟨y₀, hy₀⟩ := hε a8v1
    have hy₀T : (y₀ : G) ∈ T₀.map K.subtype :=
      (hTmem _).2 ⟨y₀, show ε y₀ ∈ a8V0 by rw [hy₀]; exact a8v1_mem_V0, rfl⟩
    have h1 := (mem_primeCoreOf_iff y₀).1 (hle hy₀T)
    rw [hO] at h1
    have h2 : ε y₀ = 1 := MonoidHom.mem_ker.1 (by rw [hεker]; exact h1)
    rw [hy₀] at h2
    exact a8v1_ne_one h2
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  exact ⟨T₀.map K.subtype, Subgroup.map_subtype_le T₀,
    IsPGroup.of_card (n := n) (by rw [hTc, hn]), hBN', hcomm_ne, hbig, hnotle⟩

noncomputable def a8E (B : Subgroup G) {ρ : ↥B →* A8} : Subgroup G :=
  ((Subgroup.zpowers a8c8).comap ρ).map B.subtype

theorem E_facts {B D : Subgroup G} (hBab : IsElemAbelian 3 B) (hDB : D ≤ B) (hDcard : Nat.card D = 9)
    {ρ : ↥B →* A8} (hρker : ∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ D) (b₁ : ↥B) (hb₁ : ρ b₁ = a8c8) :
    IsE3 3 B (a8E B (ρ := ρ)) ∧ D ≤ a8E B (ρ := ρ) := by
  set E' : Subgroup ↥B := (Subgroup.zpowers a8c8).comap ρ with hE'
  have hkerD : ρ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hρker b
  have hcard9 : Nat.card ρ.ker = 9 := by
    rw [hkerD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hDcard]
  have hrange : (ρ.comp E'.subtype).range = Subgroup.zpowers a8c8 := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩
      exact e.2
    · intro hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      refine ⟨⟨b₁ ^ n, ?_⟩, ?_⟩
      · show ρ (b₁ ^ n) ∈ Subgroup.zpowers a8c8
        rw [map_zpow, hb₁]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
      · show ρ (b₁ ^ n) = z
        rw [map_zpow, hb₁, hn]
  have hker' : (ρ.comp E'.subtype).ker = ρ.ker.subgroupOf E' := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hle' : ρ.ker ≤ E' := fun b hb => by
    show ρ b ∈ Subgroup.zpowers a8c8
    rw [MonoidHom.mem_ker.1 hb]
    exact one_mem _
  have hcardE' : Nat.card E' = 27 := by
    have h1 := card_eq_range_mul_ker (ρ.comp E'.subtype)
    rw [hrange, hker', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv, hcard9,
      Nat.card_zpowers, a8c8_orderOf] at h1
    omega
  have hE3 : IsE3 3 B (a8E B (ρ := ρ)) := by
    refine ⟨Subgroup.map_subtype_le _, isElemAbelian_mono hBab (Subgroup.map_subtype_le _), ?_⟩
    rw [a8E, Nat.card_congr (Subgroup.equivMapOfInjective E' B.subtype B.subtype_injective).toEquiv.symm,
      hcardE']
    norm_num
  refine ⟨hE3, fun d hd => ?_⟩
  have hdB : d ∈ B := hDB hd
  exact Subgroup.mem_map.2 ⟨⟨d, hdB⟩, show ρ ⟨d, hdB⟩ ∈ Subgroup.zpowers a8c8 by
    rw [(hρker ⟨d, hdB⟩).2 hd]; exact one_mem _, rfl⟩

theorem subsingleton_pSimple_bot : Subsingleton (PSimple 3 (⊥ : Subgroup G)) := by
  haveI : Subsingleton ↥(⊥ : Subgroup G) := inferInstance
  haveI : Subsingleton (PQuot 3 (⊥ : Subgroup G)) := subsingleton_quot _
  exact subsingleton_quot _

theorem layer_part {K B D X : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKX : IsSubnormal K X) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hDeq : D = B ⊓ Subgroup.centralizer (K : Set G)) (hDB : D ≤ B)
    {ε : ↥K →* A8} (hε : Function.Surjective ε) (hεker : ε.ker = Subgroup.center ↥K)
    (hc2 : Nat.card (Subgroup.center ↥K) ∣ 2)
    {ρ : ↥B →* A8}
    (hrel : ∀ (b : ↥B) (k : ↥K), ε (conjEnd K b.1 (hBN b.2) k) = ρ b * ε k * (ρ b)⁻¹)
    (hρker : ∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ D)
    (hO : GLAPPrimeCore 3 ↥K = Subgroup.center ↥K)
    (hdvd : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) (b₁ : ↥B) (hb₁ : ρ b₁ = a8c8) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer ((a8E B (ρ := ρ) : Subgroup G) : Set G)) ≠ ⊥ := by
  obtain ⟨y₁, hy₁⟩ := hε a8c8
  have hz : y₁ ^ 3 ∈ Subgroup.center ↥K := by
    rw [← hεker, MonoidHom.mem_ker, map_pow, hy₁, a8c8_cube]
  have hz2 : (y₁ ^ 3) ^ 2 = 1 := by
    have h2 : orderOf (⟨y₁ ^ 3, hz⟩ : ↥(Subgroup.center ↥K)) ∣ 2 :=
      (orderOf_dvd_natCard _).trans hc2
    have h3 := orderOf_dvd_iff_pow_eq_one.1 h2
    simpa using congrArg Subtype.val h3
  set y : ↥K := y₁ ^ 4 with hy
  have hy3 : y ^ 3 = 1 := by
    calc y ^ 3 = ((y₁ ^ 3) ^ 2) ^ 2 := by rw [hy]; group
      _ = 1 := by rw [hz2, one_pow]
  have hεy : ε y = a8c8 := by
    rw [hy, map_pow, hy₁]
    calc a8c8 ^ 4 = a8c8 ^ 3 * a8c8 := by group
      _ = a8c8 := by rw [a8c8_cube, one_mul]
  have hgN : (y : G)⁻¹ * (b₁ : G) ∈ Subgroup.normalizer (K : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer y.2)) (hBN b₁.2)
  have hcg : ∀ q : ↥K, conjEnd K ((y : G)⁻¹ * (b₁ : G)) hgN q = q := by
    intro q
    refine eq_of_central_aut hKq.1 (conjEnd K ((y : G)⁻¹ * (b₁ : G)) hgN) (fun q => ?_) q
    rw [← hεker, MonoidHom.mem_ker, map_mul, map_inv]
    have hsplit : conjEnd K ((y : G)⁻¹ * (b₁ : G)) hgN q =
        conjEnd K (y : G)⁻¹ (inv_mem (Subgroup.le_normalizer y.2))
          (conjEnd K (b₁ : G) (hBN b₁.2) q) :=
      conjEnd_mul K (inv_mem (Subgroup.le_normalizer y.2)) (hBN b₁.2) q
    have hy' : ∀ x : ↥K, ε (conjEnd K (y : G)⁻¹ (inv_mem (Subgroup.le_normalizer y.2)) x) =
        (ε y)⁻¹ * ε x * ε y := fun x => by
      rw [show conjEnd K (y : G)⁻¹ (inv_mem (Subgroup.le_normalizer y.2)) x = y⁻¹ * x * y from
        Subtype.ext (by rw [conjEnd_val]; simp [mul_assoc]), map_mul, map_mul, map_inv]
    rw [hsplit, hy', hrel b₁ q, hb₁, hεy]
    group
  have hconjb : ∀ k : ↥K, (b₁ : G) * (k : G) * (b₁ : G)⁻¹ = (y : G) * (k : G) * (y : G)⁻¹ := by
    intro k
    have hk := congrArg Subtype.val (hcg k)
    rw [conjEnd_val] at hk
    calc (b₁ : G) * k * (b₁ : G)⁻¹ = (y : G) * (((y : G)⁻¹ * (b₁ : G)) * k * ((y : G)⁻¹ * (b₁ : G))⁻¹) * (y : G)⁻¹ := by group
      _ = (y : G) * k * (y : G)⁻¹ := by rw [hk]
  have hX : K ⊓ Subgroup.centralizer ((a8E B (ρ := ρ) : Subgroup G) : Set G) =
      K ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hxK, hxE⟩
      refine ⟨hxK, ?_⟩
      have hb1E : (b₁ : G) ∈ a8E B (ρ := ρ) := Subgroup.mem_map.2 ⟨b₁, by
        show ρ b₁ ∈ Subgroup.zpowers a8c8; rw [hb₁]; exact Subgroup.mem_zpowers _, rfl⟩
      have hxb : (b₁ : G) * x = x * (b₁ : G) := hxE _ hb1E
      have hcx := hconjb ⟨x, hxK⟩
      simp only [Subtype.coe_mk] at hcx
      have h1 : (y : G) * x * (y : G)⁻¹ = x := by
        rw [← hcx, hxb]; group
      calc (y : G) * x = (y : G) * x * (y : G)⁻¹ * (y : G) := by group
        _ = x * (y : G) := by rw [h1]
    · rintro ⟨hxK, hyx⟩
      refine ⟨hxK, fun e he => ?_⟩
      obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
      have he'' : ρ e' ∈ Subgroup.zpowers a8c8 := he'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 he''
      set d : ↥B := e' * (b₁ ^ n)⁻¹ with hd
      have hdD : (d : G) ∈ D := by
        apply (hρker d).1
        rw [hd, map_mul, map_inv, map_zpow, hb₁, ← hn, mul_inv_cancel]
      have hdC : (d : G) ∈ Subgroup.centralizer (K : Set G) := by
        have h := hdD
        rw [hDeq] at h
        exact h.2
      have hdx : x * (d : G) = (d : G) * x := Subgroup.mem_centralizer_iff.1 hdC x hxK
      have h1 := hconjb ⟨x, hxK⟩
      simp only [Subtype.coe_mk] at h1
      have hyx' : (y : G) * x * (y : G)⁻¹ = x := by rw [hyx]; group
      rw [hyx'] at h1
      have hbx : (b₁ : G) * x = x * (b₁ : G) := by
        calc (b₁ : G) * x = ((b₁ : G) * x * (b₁ : G)⁻¹) * (b₁ : G) := by group
          _ = x * (b₁ : G) := by rw [h1]
      have hbn : (b₁ : G) ^ n * x = x * (b₁ : G) ^ n := Commute.zpow_left hbx n
      have heq : (e' : G) = (d : G) * (b₁ : G) ^ n := by
        rw [hd, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        group
      show (e' : G) * x = x * (e' : G)
      rw [heq]
      calc (d : G) * (b₁ : G) ^ n * x = (d : G) * ((b₁ : G) ^ n * x) := by group
        _ = (d : G) * (x * (b₁ : G) ^ n) := by rw [hbn]
        _ = ((d : G) * x) * (b₁ : G) ^ n := by group
        _ = (x * (d : G)) * (b₁ : G) ^ n := by rw [hdx]
        _ = x * ((d : G) * (b₁ : G) ^ n) := by group
  rw [hX]
  have hL : GLAPComponent 3 X K := S12.glaPComponent_of_quasisimple' Nat.prime_three hKX hKq hdvd
  obtain ⟨J, hJ, ⟨hJe⟩, -⟩ := exists_component_of_layer_lift hL ε hε (by rw [hεker, hO]) hy3
    (Kb := a8Kb) (by rw [hεy]; exact a8Kb_le_centralizer) (by rw [hεy]; exact a8_centralizer)
    (by rw [hεy]; exact a8Kb_inf_zpowers) a8Kb_simple a8Kb_nonabelian (by rw [a8Kb_card]; norm_num)
  have hJne : J ≠ ⊥ := by
    rintro rfl
    haveI := subsingleton_pSimple_bot (G := G)
    have hsub : Subsingleton ↥a8Kb := ⟨fun x y => hJe.symm.injective (Subsingleton.elim _ _)⟩
    haveI : IsSimpleGroup ↥a8Kb := a8Kb_simple
    exact (not_nontrivial_iff_subsingleton.2 hsub) inferInstance
  intro h
  have hle : J ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(y : G)} : Set G)) := le_sSup hJ
  rw [h] at hle
  exact hJne (le_bot_iff.1 hle)

theorem a8CatAt_holds (G : Type) [Group G] [Finite G] : A8CatAt G := by
  intro B x L D K hS hB81 hstd hA8
  obtain ⟨⟨⟨⟨hBmax, -, -⟩, -⟩, -, hBN⟩, -⟩ := hS
  obtain ⟨hBab, -, -⟩ := hBmax
  obtain ⟨hDB, -, hDcard, -, hKdef, hKcomp, hDeq⟩ := hstd
  have hDcard9 : Nat.card D = 9 := by rw [hDcard]; norm_num
  have hC : ∀ c : G, (∀ d ∈ D, c * d = d * c) → ∀ g ∈ Subgroup.centralizer (D : Set G),
      c * g * c⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    intro c hc g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro d hd
    have h1 : d * c⁻¹ = c⁻¹ * d := by
      have := hc d hd
      calc d * c⁻¹ = c⁻¹ * (c * d) * c⁻¹ := by group
        _ = c⁻¹ * (d * c) * c⁻¹ := by rw [hc d hd]
        _ = c⁻¹ * d := by group
    calc d * (c * g * c⁻¹) = (d * c) * g * c⁻¹ := by group
      _ = (c * d) * g * c⁻¹ := by rw [← hc d hd]
      _ = c * (d * g) * c⁻¹ := by group
      _ = c * (g * d) * c⁻¹ := by rw [hg d hd]
      _ = c * g * (d * c⁻¹) := by group
      _ = c * g * (c⁻¹ * d) := by rw [h1]
      _ = c * g * c⁻¹ * d := by group
  have hBX : B ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
    intro b hb
    have hcomm : ∀ d ∈ D, b * d = d * b := fun d hd =>
      congrArg Subtype.val (hBab.1.is_comm.comm ⟨b, hb⟩ ⟨d, hDB hd⟩)
    have hcomm' : ∀ d ∈ D, b⁻¹ * d = d * b⁻¹ := fun d hd => by
      have := hcomm d hd
      calc b⁻¹ * d = b⁻¹ * (d * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * d) * b⁻¹ := by rw [this]
        _ = d * b⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hgL, hgC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hBN hb) g).1 hgL, hC b hcomm g hgC⟩
    · rintro ⟨hbL, hbC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hBN hb) g).2 hbL, ?_⟩
      simpa [mul_assoc] using hC b⁻¹ hcomm' _ hbC
  have hBNK : B ≤ Subgroup.normalizer (K : Set G) := fun b hb => by
    rw [hKdef]
    exact S12.mem_normalizer_glaLayer' (hBX hb)
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKX : IsSubnormal K (L ⊓ Subgroup.centralizer (D : Set G)) := hKcomp.2.1
  obtain ⟨i, hi, ⟨eS⟩⟩ := hA8
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | j | s
  · exact False.elim hi
  swap
  · exact False.elim hi
  swap
  · exact False.elim hi
  have hn8 : n = 8 := hi
  subst hn8
  obtain ⟨⟨e, hO⟩, hc2⟩ := exists_iso_of_pSimple hKq eS
  have hε : Function.Surjective (piOf K e) := piOf_surjective K e
  have hεker : (piOf K e).ker = Subgroup.center ↥K := by rw [piOf_ker, hO]
  have hinner : ∀ b : ↥B, ∃ m : A8, ∀ k : ↥K,
      piOf K e (conjEnd K b.1 (hBNK b.2) k) = m * piOf K e k * m⁻¹ :=
    fun b => inner_of_pow3 e (hBNK b.2) (hBab.2 b.1 b.2)
  obtain ⟨ρ, hrel, hρker⟩ := exists_rho hKq hBNK hDeq hε hεker hinner
  have hρ3 : IsPGroup 3 ρ.range := isPGroup_three_of_pow fun x => by
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 x.2
    have hb3 : b ^ 3 = 1 := Subtype.ext (hBab.2 b.1 b.2)
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hb, ← map_pow, hb3, map_one]
  have hρcard : Nat.card ρ.range = 9 := by
    have hB := card_eq_range_mul_ker ρ
    have hkerc : Nat.card ρ.ker = 9 := by
      have hk : ρ.ker = D.subgroupOf B := by
        ext b
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hρker b
      rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hDcard9]
    obtain ⟨m, hm⟩ := hρ3.exists_card_eq
    have hdvd : 3 ^ m ∣ 20160 := by
      rw [← a8_card, ← hm]; exact Subgroup.card_subgroup_dvd_card _
    have hm2 := a8_three_part_perm m hdvd
    have hle9 : 3 ^ m ≤ 9 := by
      interval_cases m <;> norm_num
    rw [hkerc] at hB
    norm_num at hB81
    omega
  obtain ⟨ε', ρ', hε', hεker', hrel', hρ'ker, hρ'r⟩ := standardize hBNK hε hrel hρcard hρ3
  have hεkerC : ε'.ker = Subgroup.center ↥K := hεker'.trans hεker
  have hρ'ker' : ∀ b : ↥B, ρ' b = 1 ↔ (b : G) ∈ D := fun b => (hρ'ker b).trans (hρker b)
  have hdvdK : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    have h1 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ε' hε').toEquiv
    have h2 := Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hεkerC).toEquiv
    rw [a8_card] at h1
    rw [← h2, h1]
    norm_num
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : ↥B, ρ' b₁ = a8c8 := by
    have : a8c8 ∈ ρ'.range := by rw [hρ'r]; exact a8c8_mem_P0
    exact MonoidHom.mem_range.1 this
  obtain ⟨hE3, hDE⟩ := E_facts hBab hDB hDcard9 hρ'ker' b₁ hb₁
  exact ⟨T_part hBNK hε' hεkerC hc2 hO hrel' hρ'r b₁ hb₁, a8E B (ρ := ρ'), hE3, hDE,
    layer_part hKq hKX hBNK hDeq hDB hε' hεkerC hc2 hrel' hρ'ker' hO hdvdK b₁ hb₁⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB
