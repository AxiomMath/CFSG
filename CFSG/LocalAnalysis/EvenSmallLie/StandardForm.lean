module

public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelAction
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.Walter.Bender1970.S2.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.M12Cover.CyclicKernel
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem inf_centralizer_eq_center (L : Subgroup G) :
    L ⊓ centralizer (L : Set G) = (center L).map L.subtype := by
  apply le_antisymm
  · rintro x ⟨hxL, hxC⟩
    exact ⟨⟨x, hxL⟩, mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 hxC l l.2),
      rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, mem_centralizer_of_mem_center hz⟩

theorem mem_sup_centralizer_of_conj_mod_center {L : Subgroup G} (hL : commutator L = ⊤)
    {h l : G} (hl : l ∈ L)
    (hx : ∀ x ∈ L, (h * x * h⁻¹)⁻¹ * (l * x * l⁻¹) ∈ (center L).map L.subtype) :
    h ∈ L ⊔ centralizer (L : Set G) := by
  have hc : l⁻¹ * h ∈ centralizer (L : Set G) := by
    refine CFSG.Walter.mem_centralizer_of_commutator_mem_center hL fun x hxL => ?_
    obtain ⟨z, hz, hzx⟩ := hx x hxL
    have hzc : ∀ y ∈ L, y * (z : G)⁻¹ = (z : G)⁻¹ * y := fun y hy => by
      have h1 := congrArg Subtype.val (mem_center_iff.1 hz ⟨y, hy⟩)
      simp only [coe_mul] at h1
      calc y * (z : G)⁻¹ = (z : G)⁻¹ * ((z : G) * y) * (z : G)⁻¹ := by group
        _ = (z : G)⁻¹ * (y * z) * (z : G)⁻¹ := by rw [h1]
        _ = (z : G)⁻¹ * y := by group
    have e1 : h * x * h⁻¹ = l * x * l⁻¹ * (z : G)⁻¹ := by
      rw [coe_subtype] at hzx
      rw [hzx]
      group
    have key : l⁻¹ * h * x * (l⁻¹ * h)⁻¹ * x⁻¹ = (z : G)⁻¹ := by
      calc l⁻¹ * h * x * (l⁻¹ * h)⁻¹ * x⁻¹ = l⁻¹ * (h * x * h⁻¹) * l * x⁻¹ := by group
        _ = x * (l⁻¹ * (z : G)⁻¹ * l) * x⁻¹ := by rw [e1]; group
        _ = x * (z : G)⁻¹ * x⁻¹ := by
          rw [mul_assoc l⁻¹, ← hzc l hl, inv_mul_cancel_left]
        _ = (z : G)⁻¹ := by rw [hzc x hxL, mul_inv_cancel_right]
    rw [key]
    exact ⟨z⁻¹, inv_mem hz, rfl⟩
  have : h = l * (l⁻¹ * h) := by group
  rw [this]
  exact mul_mem_sup hl hc

theorem exists_hom_quotient_center_of_sup {L R H : Subgroup G}
    (hRL : R ≤ centralizer (L : Set G)) (hH : L ⊔ R = H)
    (hLR : L ⊓ R = (center L).map L.subtype) :
    ∃ θ : H →* L ⧸ center L, Function.Surjective θ ∧ θ.ker = R.subgroupOf H := by
  have hc : ∀ (l : L) (r : R), Commute (L.subtype l) (R.subtype r) := fun l r =>
    mem_centralizer_iff.1 (hRL r.2) l l.2
  set f := L.subtype.noncommCoprod R.subtype hc with hf
  have hrange : f.range = H := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype, hH]
  have hfH : ∀ p, f p ∈ H := fun p => hrange ▸ MonoidHom.mem_range.2 ⟨p, rfl⟩
  have hkey : ∀ p : L × R, f p ∈ R ↔ p.1 ∈ center L := by
    rintro ⟨l, r⟩
    rw [hf, MonoidHom.noncommCoprod_apply]
    simp only [coe_subtype]
    constructor
    · intro h
      have hl : (l : G) ∈ R := by simpa using R.mul_mem h (R.inv_mem r.2)
      obtain ⟨z, hz, hzl⟩ : (l : G) ∈ (center L).map L.subtype := hLR ▸ ⟨l.2, hl⟩
      rwa [show z = l from Subtype.ext hzl] at hz
    · intro h
      have hl : (l : G) ∈ L ⊓ R := hLR ▸ ⟨l, h, rfl⟩
      exact R.mul_mem hl.2 r.2
  set θ' : L × R →* L ⧸ center L := (QuotientGroup.mk' (center L)).comp (MonoidHom.fst L R)
  have hker : f.ker ≤ θ'.ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have hp1 : p.1 ∈ center L := (hkey p).1 (by rw [hp]; exact R.one_mem)
    simpa [θ'] using hp1
  set e := (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)
  set θ := (QuotientGroup.lift f.ker θ' hker).comp e.symm.toMonoidHom
  have hval : ∀ p : L × R, θ ⟨f p, hfH p⟩ = (p.1 : L ⧸ center L) := by
    intro p
    have he : e.symm ⟨f p, hfH p⟩ = (QuotientGroup.mk p : (L × R) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, QuotientGroup.lift_mk, θ',
      MonoidHom.coe_fst, QuotientGroup.mk'_apply]
  have hpre : ∀ h : H, ∃ p : L × R, f p = h := fun h => by
    have hh : (h : G) ∈ f.range := hrange ▸ h.2
    exact hh
  refine ⟨θ, fun q => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨f (l, 1), hfH _⟩, hval (l, 1)⟩
  · ext h
    obtain ⟨p, hp⟩ := hpre h
    obtain rfl : h = ⟨f p, hfH p⟩ := Subtype.ext hp.symm
    rw [MonoidHom.mem_ker, mem_subgroupOf, hval, QuotientGroup.eq_one_iff, hkey]

end General

section ZStar

variable {G : Type} [Group G] [Finite G]

private theorem exists_conj_ne_mem_centralizer (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t := by
  have := Fintype.ofFinite G
  by_contra hcon
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon ⟨g⁻¹, by rw [inv_inv]; exact mem_centralizer_singleton_iff.2 hg,
      by rwa [inv_inv]⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.Milestones.glauberman_zStar G t ht1 ht2 hiso
  rcases hG.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · have hz : t ∈ center G := mem_center_iff.2 fun g => by
      have h1 := hNt g
      rw [mem_bot, mul_inv_eq_one] at h1
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h1]
    rcases hG.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact ht1 (mem_bot.1 (h ▸ hz))
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
  · rw [card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)

end ZStar

section Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem std_center_facts (hset : StandardSetting G L) {t : G} (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) :
    t ∈ centralizer (L : Set G) ∧ IsCyclic (centralizer (L : Set G)) ∧
      IsPGroup 2 (centralizer (L : Set G)) ∧
      (∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = t) ∧
      centralizer ({t} : Set G) = normalizer (L : Set G) ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer (L : Set G) ≤ centralizer ({t} : Set G) := by
  obtain ⟨z, hzZ, rfl⟩ := htZ
  obtain ⟨S, hS⟩ := hset.cyclic
  have hz : orderOf (z : G) = 2 := ht
  have htC : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_of_mem_center hzZ
  obtain ⟨hC2, hCc⟩ :=
    centralizer_isPGroup_isCyclic_of_center hset.standard hzZ hz (hset.core _ hz) S hS
  have huniq : ∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = z := fun x hx hx2 =>
    eq_of_orderOf_eq_two_of_isCyclic hCc hx htC hx2 hz
  have hNt : normalizer (L : Set G) ≤ centralizer ({(z : G)} : Set G) := by
    intro n hn
    have h1 : n * z * n⁻¹ = z := huniq _ (conj_mem_centralizer_of_mem_normalizer hn htC)
      (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz])
    rw [mem_centralizer_singleton_iff]
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h1]
  refine ⟨htC, hCc, hC2, huniq,
    le_antisymm (centralizer_le_normalizer_of_standard hset.standard htC hz) hNt,
    fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl),
    fun c hc => mem_centralizer_singleton_iff.2 (mul_comm_of_isCyclic hCc hc htC)⟩

theorem std_center_involution (hset : StandardSetting G L) (hZ : center L ≠ ⊥) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ (center L).map L.subtype ∧ IsCyclic (center L) ∧
      IsPGroup 2 (center L) ∧ IsCyclic (centralizer (L : Set G)) ∧
      IsPGroup 2 (centralizer (L : Set G)) ∧
      (∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = t) ∧
      centralizer ({t} : Set G) = normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hset.cyclic
  obtain ⟨-, t₀, ht₀S, ht₀, -⟩ :=
    StandardRecognition.standard_cyclic_sylow_unique_involution hset.standard S hS
  obtain ⟨-, hZc, hZ2⟩ := StandardRecognition.standard_cyclic_local_centralizer_kernel_two_group
    hset.standard S hS ht₀S ht₀ (hset.core _ (by rwa [orderOf_coe]))
  have h2 : 2 ∣ Nat.card (center L) := by
    rcases hZ2.card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.1 h) hZ
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzG : orderOf ((z : L) : G) = 2 := by rw [orderOf_coe, orderOf_coe, hz]
  have hzZ : ((z : L) : G) ∈ (center L).map L.subtype := ⟨z, z.2, rfl⟩
  obtain ⟨-, hCc, hC2, huniq, hN, -, -⟩ := std_center_facts hset hzG hzZ
  exact ⟨_, hzG, hzZ, hZc, hZ2, hCc, hC2, huniq, hN⟩

theorem std_automizer_embedding_of_standard (hL : standardComponentIsStandard L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype) :
    ∃ θ : centralizer ({t} : Set G) →* MulAut (L ⧸ center L),
      (∀ (h : centralizer ({t} : Set G)) (l l' : L), (l' : G) = h * l * (h : G)⁻¹ →
        θ h (l : L ⧸ center L) = (l' : L ⧸ center L)) ∧
      (∀ h, θ h = 1 ↔ (h : G) ∈ centralizer (L : Set G)) ∧
      ∀ h, (∃ q : L ⧸ center L, θ h = MulAut.conj q) ↔
        (h : G) ∈ L ⊔ centralizer (L : Set G) := by
  have htC : t ∈ centralizer (L : Set G) := by
    obtain ⟨z, hzZ, rfl⟩ := htZ
    exact mem_centralizer_of_mem_center hzZ
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL.1.1
  obtain ⟨θ, hθ, hθ1⟩ := M12Cover.CyclicKernel.exists_normalizer_action
    (centralizer_le_normalizer_of_standard hL htC ht)
    (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hθl : ∀ l : L, θ ⟨l, hLt l.2⟩ = MulAut.conj (l : L ⧸ center L) := by
    intro l
    ext q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.conj_apply]
    exact hθ ⟨l, hLt l.2⟩ m (l * m * l⁻¹) rfl
  refine ⟨θ, hθ, hθ1, fun h => ⟨?_, fun hh => ?_⟩⟩
  · rintro ⟨q, hq⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : θ (⟨l, hLt l.2⟩⁻¹ * h) = 1 := by rw [map_mul, map_inv, hθl, hq, inv_mul_cancel]
    rw [hθ1] at h1
    have h2 : (h : G) = l * ((l : G)⁻¹ * h) := by group
    rw [h2]
    exact mul_mem_sup l.2 (by simpa using h1)
  · obtain ⟨k, hk, n, hn, hkn⟩ := exists_mul_of_mem_sup_of_commute
      (fun k hk n hn => mem_centralizer_iff.1 hn k hk) hh
    have hnt : n ∈ centralizer ({t} : Set G) := by
      have := (centralizer ({t} : Set G)).mul_mem (inv_mem (hLt hk)) h.2
      rwa [hkn, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have hsplit : h = ⟨k, hLt hk⟩ * ⟨n, hnt⟩ := Subtype.ext hkn
    refine ⟨(⟨k, hk⟩ : L), ?_⟩
    rw [hsplit, map_mul, (hθ1 ⟨n, hnt⟩).2 hn, mul_one]
    exact hθl ⟨k, hk⟩

theorem std_automizer_embedding (hset : StandardSetting G L) {t : G} (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) :
    ∃ θ : centralizer ({t} : Set G) →* MulAut (L ⧸ center L),
      (∀ (h : centralizer ({t} : Set G)) (l l' : L), (l' : G) = h * l * (h : G)⁻¹ →
        θ h (l : L ⧸ center L) = (l' : L ⧸ center L)) ∧
      (∀ h, θ h = 1 ↔ (h : G) ∈ centralizer (L : Set G)) ∧
      ∀ h, (∃ q : L ⧸ center L, θ h = MulAut.conj q) ↔
        (h : G) ∈ L ⊔ centralizer (L : Set G) :=
  std_automizer_embedding_of_standard hset.standard ht htZ

theorem std_centralizer_eq_sup_of_inner (hset : StandardSetting G L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) :
    centralizer ({t} : Set G) = L ⊔ centralizer (L : Set G) := by
  obtain ⟨θ, -, -, hinn⟩ := std_automizer_embedding hset ht htZ
  obtain ⟨-, -, -, -, -, hLt, hCt⟩ := std_center_facts hset ht htZ
  exact le_antisymm (fun h hh => (hinn ⟨h, hh⟩).1 (hinner _)) (sup_le hLt hCt)

theorem std_mem_sup_of_conj_mod_center (hset : StandardSetting G L) {h l : G} (hl : l ∈ L)
    (hx : ∀ x ∈ L, (h * x * h⁻¹)⁻¹ * (l * x * l⁻¹) ∈ (center L).map L.subtype) :
    h ∈ L ⊔ centralizer (L : Set G) :=
  mem_sup_centralizer_of_conj_mod_center hset.standard.1.1 hl hx

theorem std_kernel_eq_zpowers_of_central (hset : StandardSetting G L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype)
    (hcent : ∀ h ∈ centralizer ({t} : Set G), ∀ r ∈ centralizer (L : Set G), h * r = r * h)
    {J : Type*} [Group J] (θ : centralizer ({t} : Set G) →* J) (hθ : Function.Surjective θ)
    (hker : θ.ker = (centralizer (L : Set G)).subgroupOf (centralizer ({t} : Set G)))
    (hJ : ∀ v : J, orderOf v = 2 → M12Cover.NoNormalFour (centralizer ({v} : Set J))) :
    centralizer (L : Set G) = zpowers t := by
  obtain ⟨htC, hCc, hC2, -, -, -, -⟩ := std_center_facts hset ht htZ
  set R := centralizer (L : Set G) with hRdef
  have hRn : (R.subgroupOf (centralizer ({t} : Set G))).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    rw [hcent _ c.2 _ hn, mul_inv_cancel_right]
    exact hn
  have hR4 : Nat.card R < 4 := by
    by_contra h4
    push Not at h4
    obtain ⟨g, hgH, hgne⟩ := exists_conj_ne_mem_centralizer hset.simple hset.nonab ht
    have hu := mem_centralizer_singleton_iff.1 hgH
    have hh : g * t * g⁻¹ ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [hu]
        _ = t * (g * t * g⁻¹) := by group
    have hg : MulAut.conj g⁻¹ • R ≤ centralizer ({t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, MulAut.smul_def,
        MulAut.conj_apply] at hx
      have hc := hcent _ hh _ hx
      rw [mem_centralizer_singleton_iff]
      calc x * t = g⁻¹ * ((g * x * g⁻¹) * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * (g * x * g⁻¹)) * g := by rw [hc]
        _ = t * x := by group
    have hgt := (CentralCover.cyclic_centralizer_kernel_small_normal_four_obstruction hCc hC2 h4
      htC ht rfl hRn (fun h hh s hs => hcent _ (pow_mem hh 2) s hs) θ hθ hker
      (fun v hv N hN hN' => by
        obtain ⟨h1, h2⟩ := hJ v hv N hN
        rcases hN' with h | h
        · exact h.elim h1.false
        · exact h.elim h2.false) g hg).2
    apply hgne
    rw [mem_centralizer_singleton_iff] at hgt
    rw [mul_assoc, ← hgt, inv_mul_cancel_left]
  have hzR : zpowers t ≤ R := zpowers_le.2 htC
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hC2
  have hk1 : k = 1 := by
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      have : t ∈ (⊥ : Subgroup G) := hk ▸ htC
      rw [mem_bot] at this
      rw [this, orderOf_one] at ht
      exact absurd ht (by decide)
    omega
  refine (eq_of_le_of_card_ge hzR ?_).symm
  rw [hk, hk1, Nat.card_zpowers, ht, pow_one]

theorem std_kernel_eq_center_of_J_condition (hset : StandardSetting G L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype)
    (hsup : centralizer ({t} : Set G) = L ⊔ centralizer (L : Set G))
    (hJ : ∀ v : L ⧸ center L, orderOf v = 2 →
      M12Cover.NoNormalFour (centralizer ({v} : Set (L ⧸ center L)))) :
    centralizer (L : Set G) = zpowers t := by
  obtain ⟨-, hCc, -, -, -, -, -⟩ := std_center_facts hset ht htZ
  have hcent : ∀ h ∈ centralizer ({t} : Set G), ∀ r ∈ centralizer (L : Set G),
      h * r = r * h := by
    intro h hh r hr
    rw [hsup] at hh
    obtain ⟨k, hk, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun k hk n hn => mem_centralizer_iff.1 hn k hk) hh
    rw [mul_assoc, mul_comm_of_isCyclic hCc hn hr, ← mul_assoc, mem_centralizer_iff.1 hr k hk,
      mul_assoc]
  obtain ⟨θ, hθs, hθk⟩ :=
    exists_hom_quotient_center_of_sup le_rfl hsup.symm (inf_centralizer_eq_center L)
  exact std_kernel_eq_zpowers_of_central hset ht htZ hcent θ hθs hθk hJ

theorem std_centralizer_eq_of_J_condition (hset : StandardSetting G L) {t : G}
    (ht : orderOf t = 2) (htZ : t ∈ (center L).map L.subtype)
    (hsup : centralizer ({t} : Set G) = L ⊔ centralizer (L : Set G))
    (hJ : ∀ v : L ⧸ center L, orderOf v = 2 →
      M12Cover.NoNormalFour (centralizer ({v} : Set (L ⧸ center L)))) :
    centralizer (L : Set G) = zpowers t ∧ (center L).map L.subtype = zpowers t ∧
      Nat.card (center L) = 2 ∧ centralizer ({t} : Set G) = L := by
  have hC := std_kernel_eq_center_of_J_condition hset ht htZ hsup hJ
  have htL : t ∈ L := by
    obtain ⟨z, -, rfl⟩ := htZ
    exact z.2
  have hzL : zpowers t ≤ L := zpowers_le.2 htL
  have hZ : (center L).map L.subtype = zpowers t := by
    rw [← inf_centralizer_eq_center, hC, inf_of_le_right hzL]
  refine ⟨hC, hZ, ?_, by rw [hsup, hC, sup_of_le_left hzL]⟩
  rw [← card_map_of_injective L.subtype_injective, hZ, Nat.card_zpowers, ht]

theorem std_standard_form_of_inner (hset : StandardSetting G L) (hZ : center L ≠ ⊥)
    (hinner : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q)
    (hJ : ∀ v : L ⧸ center L, orderOf v = 2 →
      M12Cover.NoNormalFour (centralizer ({v} : Set (L ⧸ center L)))) :
    ∃ t : G, orderOf t = 2 ∧ centralizer (L : Set G) = zpowers t ∧
      (center L).map L.subtype = zpowers t ∧ Nat.card (center L) = 2 ∧
      centralizer ({t} : Set G) = L := by
  obtain ⟨t, ht, htZ, -⟩ := std_center_involution hset hZ
  exact ⟨t, ht, std_centralizer_eq_of_J_condition hset ht htZ
    (std_centralizer_eq_sup_of_inner hset ht htZ hinner) hJ⟩

end Std

end CFSG.EvenSmallLie
