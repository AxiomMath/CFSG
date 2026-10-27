module

public import CFSG.Quasithin.Background.C116Two.FixModLift

public section

namespace CFSG.QuasithinUnique.L246C127.Deg

open CFSG.Quasithin.C116Two CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {V : Type} [CommGroup V]

theorem conj_mem_blockU {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) {u : G}
    (hu : u ∈ blockU K) : n * u * n⁻¹ ∈ blockU K :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hn) u).mp hu

theorem conj_mem_blockZ {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) {u : G}
    (hu : u ∈ blockZ K) : n * u * n⁻¹ ∈ blockZ K :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ hn) u).mp hu

@[expose] noncomputable def sinv (D : ModData K V) (v : V) : ↥(blockU K) := Function.surjInv D.surj v

@[expose] def cU {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) (u : ↥(blockU K)) : ↥(blockU K) :=
  ⟨n * (u : G) * n⁻¹, conj_mem_blockU hn u.2⟩

@[expose] noncomputable def gfun (D : ModData K V) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (v : V) : V :=
  D.β (cU hn (sinv D v))

theorem gfun_β (D : ModData K V) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (u : ↥(blockU K)) : gfun D hn (D.β u) = D.β (cU hn u) := by
  set u' := sinv D (D.β u) with hu'
  have h1 : D.β u' = D.β u := Function.surjInv_eq D.surj (D.β u)
  have h2 : u'⁻¹ * u ∈ D.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [D.ker, Subgroup.mem_subgroupOf] at h2
  have h3 : n * ((u' : G)⁻¹ * (u : G)) * n⁻¹ ∈ blockZ K := conj_mem_blockZ hn h2
  have h4 : (cU hn u')⁻¹ * cU hn u ∈ D.β.ker := by
    rw [D.ker, Subgroup.mem_subgroupOf]
    have : (((cU hn u')⁻¹ * cU hn u : ↥(blockU K)) : G) = n * ((u' : G)⁻¹ * (u : G)) * n⁻¹ := by
      simp only [cU, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact h3
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h4
  unfold gfun
  exact h4

theorem cU_val {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) (u : ↥(blockU K)) :
    ((cU hn u : ↥(blockU K)) : G) = n * (u : G) * n⁻¹ := rfl

@[expose] noncomputable def gammaAut (D : ModData K V) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    MulAut V where
  toFun := gfun D hn
  invFun := gfun D ((Subgroup.normalizer (K : Set G)).inv_mem hn)
  left_inv v := by
    obtain ⟨u, rfl⟩ := D.surj v
    rw [gfun_β, gfun_β]
    congr 1
    apply Subtype.ext
    simp only [cU_val]
    group
  right_inv v := by
    obtain ⟨u, rfl⟩ := D.surj v
    rw [gfun_β, gfun_β]
    congr 1
    apply Subtype.ext
    simp only [cU_val]
    group
  map_mul' a b := by
    obtain ⟨u, rfl⟩ := D.surj a
    obtain ⟨u', rfl⟩ := D.surj b
    rw [← map_mul, gfun_β, gfun_β, gfun_β, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [cU_val, Subgroup.coe_mul]
    group

theorem gammaAut_apply (D : ModData K V) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (u : ↥(blockU K)) : gammaAut D hn (D.β u) = D.β (cU hn u) := gfun_β D hn u

theorem gammaAut_one (D : ModData K V) :
    gammaAut D (Subgroup.normalizer (K : Set G)).one_mem = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := D.surj v
  rw [gammaAut_apply]
  show D.β _ = D.β u
  congr 1
  apply Subtype.ext
  simp only [cU_val]
  group

theorem gammaAut_mul (D : ModData K V) {n m : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hm : m ∈ Subgroup.normalizer (K : Set G)) :
    gammaAut D ((Subgroup.normalizer (K : Set G)).mul_mem hn hm) = gammaAut D hn * gammaAut D hm := by
  apply MulEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := D.surj v
  rw [gammaAut_apply, MulAut.mul_apply, gammaAut_apply, gammaAut_apply]
  congr 1
  apply Subtype.ext
  simp only [cU_val]
  group

@[expose] noncomputable def gammaHom (D : ModData K V) : ↥(Subgroup.normalizer (K : Set G)) →* MulAut V where
  toFun n := gammaAut D n.2
  map_one' := gammaAut_one D
  map_mul' a b := gammaAut_mul D a.2 b.2

theorem gammaAut_conj_rho (D : ModData K V) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (k : ↥K) :
    gammaAut D hn * D.ρ k * (gammaAut D hn)⁻¹ =
      D.ρ ⟨n * (k : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn k).mp k.2⟩ := by
  have hinv : (gammaAut D hn)⁻¹ = gammaAut D ((Subgroup.normalizer (K : Set G)).inv_mem hn) := by
    rw [inv_eq_iff_mul_eq_one, ← gammaAut_mul, ← gammaAut_one D]
    congr 1
    simp
  apply MulEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := D.surj v
  rw [hinv, MulAut.mul_apply, MulAut.mul_apply, gammaAut_apply]
  set u₁ := cU ((Subgroup.normalizer (K : Set G)).inv_mem hn) u with hu₁
  have e1 : D.ρ k (D.β u₁) = D.β ⟨(k : G) * (u₁ : G) * (k : G)⁻¹, by
      exact (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K k.2) u₁).mp u₁.2⟩ :=
    (D.equiv k u₁ _ rfl).symm
  rw [e1, gammaAut_apply]
  have e2 : D.β (cU hn ⟨(k : G) * (u₁ : G) * (k : G)⁻¹, by
      exact (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K k.2) u₁).mp u₁.2⟩) =
      D.ρ ⟨n * (k : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn k).mp k.2⟩ (D.β u) := by
    refine D.equiv _ u _ ?_
    simp only [cU_val, hu₁, cU, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact e2

end

section

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {V : Type} [CommGroup V]

theorem h5_centralizer_of_mem_blockZ {z : G} (hz : z ∈ blockZ K) :
    z ∈ Subgroup.centralizer (K : Set G) :=
  (show z ∈ blockU K ⊓ Subgroup.centralizer (K : Set G) from hz).2

theorem h5_comm_mem_blockZ (D : ModData K V) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (h : gammaAut D hn = 1) {x : G}
    (hx : x ∈ blockU K) : n * x * n⁻¹ * x⁻¹ ∈ blockZ K := by
  have h1 : D.β (cU hn ⟨x, hx⟩) = D.β ⟨x, hx⟩ := by
    have := gammaAut_apply D hn ⟨x, hx⟩
    rw [h, MulAut.one_apply] at this
    exact this.symm
  have h2 : cU hn ⟨x, hx⟩ * (⟨x, hx⟩ : ↥(blockU K))⁻¹ ∈ D.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  rw [D.ker, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem h5_conj_comm_K (D : ModData K V) (hK : IsShort2 K) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (h : gammaAut D hn = 1) {k : G} (hk : k ∈ K)
    {x : G} (hx : x ∈ blockU K) : n * (k * x * k⁻¹) * n⁻¹ = k * (n * x * n⁻¹) * k⁻¹ := by
  have hk' : n * k * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn k).mp hk
  have hρ : D.ρ ⟨k, hk⟩ = D.ρ ⟨n * k * n⁻¹, hk'⟩ := by
    have := gammaAut_conj_rho D hn ⟨k, hk⟩
    simp only [h, inv_one, mul_one, one_mul] at this
    exact this
  have hQ : k⁻¹ * (n * k * n⁻¹) ∈ blockQ K := by
    have h1 : D.ρ ((⟨k, hk⟩ : ↥K)⁻¹ * (⟨n * k * n⁻¹, hk'⟩ : ↥K)) = 1 := by
      rw [map_mul, map_inv, hρ, inv_mul_cancel]
    exact D.faithful _ h1
  have hy : n * x * n⁻¹ ∈ blockU K := conj_mem_blockU hn hx
  have hcomm : (n * x * n⁻¹) * (k⁻¹ * (n * k * n⁻¹)) = (k⁻¹ * (n * k * n⁻¹)) * (n * x * n⁻¹) :=
    C1.blockU_comm hK _ hy _ hQ
  generalize hq : k⁻¹ * (n * k * n⁻¹) = q at hQ hcomm
  have hkq : n * k * n⁻¹ = k * q := by
    rw [← hq]
    group
  calc n * (k * x * k⁻¹) * n⁻¹
      = (n * k * n⁻¹) * (n * x * n⁻¹) * (n * k * n⁻¹)⁻¹ := by group
    _ = (k * q) * (n * x * n⁻¹) * (k * q)⁻¹ := by rw [hkq]
    _ = k * (q * (n * x * n⁻¹) * q⁻¹) * k⁻¹ := by group
    _ = k * ((n * x * n⁻¹) * q * q⁻¹) * k⁻¹ := by rw [← hcomm]
    _ = k * (n * x * n⁻¹) * k⁻¹ := by group

theorem conj_eq_of_gammaAut_eq_one (D : ModData K V) (hK : IsShort2 K) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (h : gammaAut D hn = 1) :
    ∀ u ∈ blockU K, n * u * n⁻¹ = u := by
  have hcomm : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a :=
    fun a ha b hb => (C1.elemAb2_blockU hK).1 a ha b hb
  have hZ : ∀ x ∈ blockU K, n * x * n⁻¹ * x⁻¹ ∈ blockZ K :=
    fun x hx => h5_comm_mem_blockZ D hn h hx
  have hZcent : ∀ z ∈ blockZ K, ∀ k ∈ K, k * z = z * k := fun z hz k hk =>
    Subgroup.mem_centralizer_iff.mp (h5_centralizer_of_mem_blockZ hz) k hk
  have hinv : ∀ k ∈ K, ∀ x ∈ blockU K,
      n * (k * x * k⁻¹) * n⁻¹ * (k * x * k⁻¹)⁻¹ = n * x * n⁻¹ * x⁻¹ := by
    intro k hk x hx
    have hcent : k * (n * x * n⁻¹ * x⁻¹) = (n * x * n⁻¹ * x⁻¹) * k :=
      hZcent _ (hZ x hx) k hk
    rw [h5_conj_comm_K D hK hn h hk hx]
    calc k * (n * x * n⁻¹) * k⁻¹ * (k * x * k⁻¹)⁻¹
        = k * (n * x * n⁻¹ * x⁻¹) * k⁻¹ := by group
      _ = (n * x * n⁻¹ * x⁻¹) * k * k⁻¹ := by rw [hcent]
      _ = n * x * n⁻¹ * x⁻¹ := by group
  have hinvU : ∀ u ∈ blockU K, n * u⁻¹ * n⁻¹ * u⁻¹⁻¹ = (n * u * n⁻¹ * u⁻¹)⁻¹ := by
    intro u hu
    have hc := hcomm u hu _ (inv_mem (conj_mem_blockU hn hu))
    calc n * u⁻¹ * n⁻¹ * u⁻¹⁻¹ = (n * u * n⁻¹)⁻¹ * u := by group
      _ = u * (n * u * n⁻¹)⁻¹ := hc.symm
      _ = (n * u * n⁻¹ * u⁻¹)⁻¹ := by group
  have hfix : ∀ u ∈ blockU K, ∀ k ∈ K, n * ⁅u, k⁆ * n⁻¹ = ⁅u, k⁆ := by
    intro u hu k hk
    have hkey : (n * u * n⁻¹) * (n * u * n⁻¹ * u⁻¹)⁻¹ = u := by
      have hc := hcomm u hu _ (inv_mem (conj_mem_blockU hn hu))
      calc (n * u * n⁻¹) * (n * u * n⁻¹ * u⁻¹)⁻¹
          = (n * u * n⁻¹) * (u * (n * u * n⁻¹)⁻¹) := by group
        _ = (n * u * n⁻¹) * ((n * u * n⁻¹)⁻¹ * u) := by rw [hc]
        _ = u := by group
    have hzw : n * (k * u⁻¹ * k⁻¹) * n⁻¹ * (k * u⁻¹ * k⁻¹)⁻¹ = (n * u * n⁻¹ * u⁻¹)⁻¹ :=
      (hinv k hk u⁻¹ (inv_mem hu)).trans (hinvU u hu)
    have hB : n * (k * u⁻¹ * k⁻¹) * n⁻¹ = (n * u * n⁻¹ * u⁻¹)⁻¹ * (k * u⁻¹ * k⁻¹) := by
      calc n * (k * u⁻¹ * k⁻¹) * n⁻¹
          = (n * (k * u⁻¹ * k⁻¹) * n⁻¹ * (k * u⁻¹ * k⁻¹)⁻¹) * (k * u⁻¹ * k⁻¹) := by group
        _ = (n * u * n⁻¹ * u⁻¹)⁻¹ * (k * u⁻¹ * k⁻¹) := by rw [hzw]
    rw [commutatorElement_def]
    calc n * (u * k * u⁻¹ * k⁻¹) * n⁻¹
        = (n * u * n⁻¹) * (n * (k * u⁻¹ * k⁻¹) * n⁻¹) := by group
      _ = (n * u * n⁻¹) * ((n * u * n⁻¹ * u⁻¹)⁻¹ * (k * u⁻¹ * k⁻¹)) := by rw [hB]
      _ = ((n * u * n⁻¹) * (n * u * n⁻¹ * u⁻¹)⁻¹) * (k * u⁻¹ * k⁻¹) := by group
      _ = u * (k * u⁻¹ * k⁻¹) := by rw [hkey]
      _ = u * k * u⁻¹ * k⁻¹ := by group
  have hT : blockU K ≤ Subgroup.centralizer ({n} : Set G) ⊓ blockU K := by
    have hle : ⁅blockU K, K⁆ ≤ Subgroup.centralizer ({n} : Set G) ⊓ blockU K := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      refine Subgroup.mem_inf.mpr ⟨?_, C1.commutator_blockU_le K
        (Subgroup.commutator_mem_commutator hu hk)⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      calc n * ⁅u, k⁆ = n * ⁅u, k⁆ * n⁻¹ * n := by group
        _ = ⁅u, k⁆ * n := by rw [hfix u hu k hk]
    rw [C1.commutator_blockU hK] at hle
    exact hle
  intro u hu
  have hnu : n * u = u * n :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hT hu)).1 n (Set.mem_singleton n)
  calc n * u * n⁻¹ = u * n * n⁻¹ := by rw [hnu]
    _ = u := by group

end

section

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {V : Type} [CommGroup V]

@[expose] noncomputable def gamB (D : ModData K V) (A : Subgroup G) (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup (MulAut V) :=
  ((gammaHom D).comp (Subgroup.inclusion hAN)).range

theorem mem_gamB (D : ModData K V) {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G))
    {b : MulAut V} : b ∈ gamB D A hAN ↔ ∃ (a : G) (ha : a ∈ A), gammaAut D (hAN ha) = b := by
  unfold gamB
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem gammaAut_mem_gamB (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) {a : G} (ha : a ∈ A) :
    gammaAut D (hAN ha) ∈ gamB D A hAN :=
  (mem_gamB D hAN).2 ⟨a, ha, rfl⟩

@[expose] noncomputable def phiA (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) : ↥A →* MulAut V :=
  (gammaHom D).comp (Subgroup.inclusion hAN)

theorem mem_gamB_phiA (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) {b : MulAut V} :
    b ∈ gamB D A hAN ↔ ∃ a : ↥A, phiA D hAN a = b := by
  unfold gamB
  exact MonoidHom.mem_range

theorem gamB_isElemAbelian (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (gamB D A hAN) := by
  haveI : IsMulCommutative ↥A := hA.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · show x * y = y * x
    apply Subtype.ext
    obtain ⟨a, ha⟩ := (mem_gamB_phiA D hAN).1 x.2
    obtain ⟨b, hb⟩ := (mem_gamB_phiA D hAN).1 y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm' a b]
  · obtain ⟨a, ha⟩ := (mem_gamB_phiA D hAN).1 hx
    have ha2 : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA.2 _ a.2)
    rw [← ha, ← map_pow, ha2, map_one]

theorem card_blockZ_mul_card_V (D : ModData K V) :
    Nat.card ↥(blockZ K) * Nat.card V = Nat.card ↥(blockU K) := by
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hV : Nat.card V = D.β.ker.index :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective D.β D.surj).toEquiv).symm
  have hk : Nat.card ↥D.β.ker = Nat.card ↥(blockZ K) := by
    rw [D.ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rw [← Subgroup.card_mul_index (H := D.β.ker), hk, ← hV]

theorem conj_fix_of_mem_centralizer {A : Subgroup G} {a : G} (ha : a ∈ A) {s : G}
    (hs : s ∈ Subgroup.centralizer (A : Set G)) : a * s * a⁻¹ = s := by
  have h := Subgroup.mem_centralizer_iff.mp hs a (SetLike.mem_coe.2 ha)
  rw [h, mul_inv_cancel_right]

@[expose] def incS (A : Subgroup G) : ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) →* ↥(blockU K) :=
  Subgroup.inclusion inf_le_left

@[expose] noncomputable def betaS (D : ModData K V) (A : Subgroup G) :
    ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) →* V :=
  D.β.comp (incS A)

theorem cU_inter_fix {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G))
    {a : G} (ha : a ∈ A) (s : ↥(blockU K ⊓ Subgroup.centralizer (A : Set G))) :
    cU (hAN ha) (incS A s) = incS A s := by
  apply Subtype.ext
  exact conj_fix_of_mem_centralizer ha (Subgroup.mem_inf.1 s.2).2

theorem betaS_ker_mem (D : ModData K V) {A : Subgroup G}
    (s : ↥(blockU K ⊓ Subgroup.centralizer (A : Set G))) (hs : betaS D A s = 1) :
    (s : G) ∈ blockZ K := by
  have h2 : incS A s ∈ D.β.ker := MonoidHom.mem_ker.2 hs
  rw [D.ker, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem fixes_betaS_range (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (v : V) (hv : v ∈ (betaS D A).range) :
    ∀ b ∈ gamB D A hAN, b v = v := by
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hv
  intro b hb
  obtain ⟨a, ha, rfl⟩ := (mem_gamB D hAN).1 hb
  show gammaAut D (hAN ha) (D.β (incS A s)) = D.β (incS A s)
  rw [gammaAut_apply, cU_inter_fix hAN ha s]

theorem card_inter_le (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(blockZ K) * Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x} := by
  haveI : Finite V := Finite.of_surjective D.β D.surj
  have hmem : ∀ x : ↥(betaS D A).ker, (x.1 : G) ∈ blockZ K := fun x =>
    betaS_ker_mem D x.1 (MonoidHom.mem_ker.1 x.2)
  have hker : Nat.card ↥(betaS D A).ker ≤ Nat.card ↥(blockZ K) := by
    apply Nat.card_le_card_of_injective
      (fun x : ↥(betaS D A).ker => (⟨(x.1 : G), hmem x⟩ : ↥(blockZ K)))
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hrng : Nat.card ↥(betaS D A).range ≤
      Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x} := by
    apply Nat.card_le_card_of_injective
      (fun v : ↥(betaS D A).range =>
        (⟨v.1, fixes_betaS_range D hAN v.1 v.2⟩ : {x : V // ∀ b ∈ gamB D A hAN, b x = x}))
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  have hS : Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(betaS D A).ker * Nat.card ↥(betaS D A).range := by
    rw [← Subgroup.index_ker (betaS D A), Subgroup.card_mul_index]
  rw [hS]
  exact Nat.mul_le_mul hker hrng

theorem relIndex_le_card_gamB (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hconj : ∀ (n : G) (hn : n ∈ Subgroup.normalizer (K : Set G)), gammaAut D hn = 1 →
      ∀ u ∈ blockU K, n * u * n⁻¹ = u) :
    (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A ≤ Nat.card (gamB D A hAN) := by
  have hle : (phiA D hAN).ker ≤ (A ⊓ Subgroup.centralizer (blockU K : Set G)).subgroupOf A := by
    intro x hx
    have h1 : gammaAut D (hAN x.2) = 1 := MonoidHom.mem_ker.1 hx
    have h2 := hconj (x : G) (hAN x.2) h1
    refine Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩)
    exact (mul_inv_eq_iff_eq_mul.1 (h2 u hu)).symm
  calc (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A
      = ((A ⊓ Subgroup.centralizer (blockU K : Set G)).subgroupOf A).index := rfl
    _ ≤ (phiA D hAN).ker.index := Subgroup.index_antitone hle
    _ = Nat.card (gamB D A hAN) := Subgroup.index_ker (phiA D hAN)

theorem offender_transfer (D : ModData K V) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hconj : ∀ (n : G) (hn : n ∈ Subgroup.normalizer (K : Set G)), gammaAut D hn = 1 →
      ∀ u ∈ blockU K, n * u * n⁻¹ = u)
    (hoff : Nat.card (blockU K) ≤ (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A *
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G))) :
    Nat.card V ≤ Nat.card (gamB D A hAN) *
      Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x} := by
  haveI : Finite V := Finite.of_surjective D.β D.surj
  haveI : Nonempty ↥(blockZ K) := ⟨1⟩
  have hU : Nat.card ↥(blockZ K) * Nat.card V = Nat.card ↥(blockU K) :=
    card_blockZ_mul_card_V D
  have hS := card_inter_le D hAN
  have hR := relIndex_le_card_gamB D hAN hconj
  have key : Nat.card ↥(blockZ K) * Nat.card V ≤
      Nat.card ↥(blockZ K) *
        (Nat.card (gamB D A hAN) * Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x}) := by
    calc Nat.card ↥(blockZ K) * Nat.card V = Nat.card ↥(blockU K) := hU
      _ ≤ (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A *
            Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)) := hoff
      _ ≤ Nat.card (gamB D A hAN) *
            (Nat.card ↥(blockZ K) * Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x}) :=
          Nat.mul_le_mul hR hS
      _ = Nat.card ↥(blockZ K) *
            (Nat.card (gamB D A hAN) * Nat.card {x : V // ∀ b ∈ gamB D A hAN, b x = x}) := by
          ring
  exact le_of_mul_le_mul_left key (Nat.card_pos : 0 < Nat.card ↥(blockZ K))

end

section

variable {G : Type} [Group G] [Finite G]

theorem gammaAut_normalizes {K : Subgroup G} {F : Type} [Field F] [Fintype F]
    (D : ModData K (Multiplicative (Fin 2 → F))) (hrange : D.ρ.range = (slAct F).range)
    {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    ∀ l ∈ (slAct F).range, gammaAut D hn * l * (gammaAut D hn)⁻¹ ∈ (slAct F).range := by
  intro l hl
  rw [← hrange] at hl
  obtain ⟨k, rfl⟩ := hl
  rw [gammaAut_conj_rho, ← hrange]
  exact ⟨_, rfl⟩

theorem gamB_normalizes {K : Subgroup G} {F : Type} [Field F] [Fintype F]
    (D : ModData K (Multiplicative (Fin 2 → F))) (hrange : D.ρ.range = (slAct F).range)
    {A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (K : Set G)) :
    ∀ b ∈ gamB D A hAN, ∀ l ∈ (slAct F).range, b * l * b⁻¹ ∈ (slAct F).range := by
  intro b hb l hl
  obtain ⟨a, ha, rfl⟩ := (mem_gamB D hAN).1 hb
  exact gammaAut_normalizes D hrange (hAN ha) l hl

theorem gammaAut_inv {K : Subgroup G} {V : Type} [CommGroup V] (D : ModData K V) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    gammaAut D ((Subgroup.normalizer (K : Set G)).inv_mem hn) = (gammaAut D hn)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← gammaAut_mul, ← gammaAut_one D]
  congr 1
  simp

theorem comm_eq_inv {K : Subgroup G} (hK : IsShort2 K) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (u : ↥(blockU K)) :
    ⁅(u : G), a⁆ = ((u : G)⁻¹ * (a * u * a⁻¹))⁻¹ := by
  have hc : Commute (u : G) (a * (u : G) * a⁻¹) :=
    (C1.elemAb2_blockU hK).1 u u.2 _ (conj_mem_blockU ha u.2)
  have hc' : Commute (u : G) (a * (u : G) * a⁻¹)⁻¹ := hc.inv_right
  have e1 : (a * (u : G) * a⁻¹)⁻¹ = a * (u : G)⁻¹ * a⁻¹ := by group
  rw [e1] at hc'
  simp only [commutatorElement_def]
  calc (u : G) * a * (u : G)⁻¹ * a⁻¹ = (u : G) * (a * (u : G)⁻¹ * a⁻¹) := by group
    _ = (a * (u : G)⁻¹ * a⁻¹) * (u : G) := hc'.eq
    _ = ((u : G)⁻¹ * (a * u * a⁻¹))⁻¹ := by group

theorem fixed_iff_comm_mem_blockZ {K : Subgroup G} {V : Type} [CommGroup V] (D : ModData K V)
    (hK : IsShort2 K) {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G)) (u : ↥(blockU K)) :
    gammaAut D ha (D.β u) = D.β u ↔ ⁅(u : G), a⁆ ∈ blockZ K := by
  rw [gammaAut_apply, comm_eq_inv hK ha u]
  have h2 : ((u⁻¹ * cU ha u : ↥(blockU K)) : G) = (u : G)⁻¹ * (a * u * a⁻¹) := rfl
  constructor
  · intro h
    have h1 : (u⁻¹ * cU ha u : ↥(blockU K)) ∈ D.β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [D.ker, Subgroup.mem_subgroupOf, h2] at h1
    exact (blockZ K).inv_mem h1
  · intro h
    have h1 : (u⁻¹ * cU ha u : ↥(blockU K)) ∈ D.β.ker := by
      rw [D.ker, Subgroup.mem_subgroupOf, h2]
      have := (blockZ K).inv_mem h
      rwa [inv_inv] at this
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm

theorem lift_fixed {K : Subgroup G} {V : Type} [CommGroup V] (D : ModData K V) {H A : Subgroup G}
    (hKP : IsChiBlock H K) (hA : IsElemAbelian 2 A) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hoff : Nat.card (blockU K) ≤ (A ⊓ Subgroup.centralizer (blockU K : Set G)).relIndex A *
      Nat.card ↥(blockU K ⊓ Subgroup.centralizer (A : Set G)))
    (u : ↥(blockU K)) (hu : ∀ a (ha : a ∈ A), gammaAut D (hAN ha) (D.β u) = D.β u) :
    ∀ a ∈ A, (u : G) * a = a * (u : G) := by
  refine C116Two.fixMod_le_centralizer hKP hA hAN hoff u u.2 (fun a ha => ?_)
  exact (fixed_iff_comm_mem_blockZ D hKP.1.1 (hAN ha) u).1 (hu a ha)

theorem conj_eq_of_gammaAut_eq {K : Subgroup G} {V : Type} [CommGroup V] (D : ModData K V)
    (hconj : ∀ (n : G) (hn : n ∈ Subgroup.normalizer (K : Set G)), gammaAut D hn = 1 →
      ∀ u ∈ blockU K, n * u * n⁻¹ = u)
    {n a : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) (ha : a ∈ Subgroup.normalizer (K : Set G))
    (h : gammaAut D hn = gammaAut D ha) : ∀ u ∈ blockU K, n * u * n⁻¹ = a * u * a⁻¹ := by
  intro u hu
  have hm : a⁻¹ * n ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem ((Subgroup.normalizer (K : Set G)).inv_mem ha) hn
  have h1 : gammaAut D hm = 1 := by
    rw [show gammaAut D hm = gammaAut D ((Subgroup.normalizer (K : Set G)).inv_mem ha) *
      gammaAut D hn from gammaAut_mul D ((Subgroup.normalizer (K : Set G)).inv_mem ha) hn, gammaAut_inv D ha, h, inv_mul_cancel]
  have h2 := hconj _ hm h1 u hu
  have : n * u * n⁻¹ = a * ((a⁻¹ * n) * u * (a⁻¹ * n)⁻¹) * a⁻¹ := by group
  rw [this, h2]

end

end CFSG.QuasithinUnique.L246C127.Deg
