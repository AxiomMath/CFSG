module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1Norm
public import CFSG.GH74.GLS.Stage4.T2F1LocTor
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx66
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx71

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.Semidihedral CFSG.GH74.GLS.IVK
open scoped commutatorElement Pointwise

section Abstract

theorem eq_one_of_conj_eq_mul {Q : Type*} [Group Q] {c s y : Q} (hcy : c * y = y * c)
    (hs : c * s * c⁻¹ = y * s) {k : ℕ} (hk : Odd k) (hck : c ^ k = 1) {a : ℕ} (hy : y ^ 2 ^ a = 1) :
    y = 1 := by
  have hn : ∀ n : ℕ, c ^ n * s * (c ^ n)⁻¹ = y ^ n * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcyn : c * y ^ n = y ^ n * c := (Commute.pow_right hcy n).eq
      calc c ^ (n + 1) * s * (c ^ (n + 1))⁻¹ = c * (c ^ n * s * (c ^ n)⁻¹) * c⁻¹ := by group
        _ = c * y ^ n * s * c⁻¹ := by rw [ih]; group
        _ = y ^ n * (c * s * c⁻¹) := by rw [hcyn]; group
        _ = y ^ (n + 1) * s := by rw [hs, pow_succ]; group
  have h1 : y ^ k = 1 := by
    have h := hn k
    rw [hck, one_mul, inv_one, mul_one] at h
    have h' : y ^ k * s = 1 * s := by rw [one_mul]; exact h.symm
    exact mul_right_cancel h'
  have h2 : orderOf y ∣ Nat.gcd k (2 ^ a) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hy)
  rw [((Nat.coprime_two_right.2 hk).pow_right a).gcd_eq_one, Nat.dvd_one] at h2
  exact orderOf_eq_one_iff.1 h2

theorem conj_eq_of_cyclic_two {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q} (hA : IsCyclic ↥A)
    {f : Q} (hfA : ∀ x ∈ A, f * x * f⁻¹ ∈ A) {r : ℕ} (hr : Odd r) (hfr : f ^ r = 1)
    {x : Q} (hxA : x ∈ A) {a : ℕ} (hx : x ^ 2 ^ a = 1) : f * x * f⁻¹ = x := by
  have hfx : f * x * f⁻¹ ∈ zpowers x := by
    have hord : orderOf (⟨f * x * f⁻¹, hfA x hxA⟩ : ↥A) = orderOf (⟨x, hxA⟩ : ↥A) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      have := (MulAut.conj f).orderOf_eq x
      rwa [MulAut.conj_apply] at this
    have heq : zpowers (⟨f * x * f⁻¹, hfA x hxA⟩ : ↥A) = zpowers (⟨x, hxA⟩ : ↥A) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hord]
    have hmem : (⟨f * x * f⁻¹, hfA x hxA⟩ : ↥A) ∈ zpowers (⟨x, hxA⟩ : ↥A) := by
      rw [← heq]; exact mem_zpowers _
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hD : ∀ y ∈ zpowers x, f * y * f⁻¹ ∈ zpowers x := by
    rintro _ ⟨n, rfl⟩
    show f * x ^ n * f⁻¹ ∈ zpowers x
    rw [← conj_zpow]
    exact zpow_mem hfx n
  refine Stage4.Rest.F1Loc.cyclic_odd_conj_trivial (C := zpowers x) inferInstance hD hr hfr ?_ x
    (mem_zpowers x)
  intro y hy hyo
  obtain ⟨n, rfl⟩ := hy
  have hy2 : (x ^ n) ^ 2 ^ a = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have h2 : orderOf (x ^ n) ∣ Nat.gcd (orderOf (x ^ n)) (2 ^ a) :=
    Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hy2)
  rw [((Nat.coprime_two_right.2 hyo).pow_right a).gcd_eq_one, Nat.dvd_one] at h2
  show f * x ^ n * f⁻¹ = x ^ n
  rw [orderOf_eq_one_iff.1 h2]
  group

theorem sl2_cent_cyclic_sub {Γ : Type*} [Group Γ] (A : Subgroup Γ) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (φ : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) F) {z a : Γ}
    (hzA : z ∈ A) (haA : a ∈ A) (hz : orderOf z = 2) (hc : ∀ g : Γ, g * z = z * g)
    (haz : a * a = z) : IsCyclic ↥(A ⊓ centralizer ({a} : Set Γ)) := by
  obtain ⟨-, hφz⟩ := sl_central_involution φ ⟨z, hzA⟩ (by rw [Subgroup.orderOf_mk]; exact hz)
    (fun k => Subtype.ext (hc k))
  have hφa : φ ⟨a, haA⟩ * φ ⟨a, haA⟩ = OddFieldSL2.minusIdentity F := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext haz
  obtain ⟨hcyc, -, -⟩ := L2Torus.centralizer_cyclic_card hodd (φ ⟨a, haA⟩) hφa
  let f : ↥(A ⊓ centralizer ({a} : Set Γ)) →*
      ↥(Subgroup.centralizer ({φ ⟨a, haA⟩} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    (φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left)).codRestrict _ (fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (x : Γ) * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
      show φ ⟨x, x.2.1⟩ * φ ⟨a, haA⟩ = φ ⟨a, haA⟩ * φ ⟨x, x.2.1⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hx)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : φ ⟨x, x.2.1⟩ = φ ⟨y, y.2.1⟩ := congrArg Subtype.val hxy
    have h2 : (⟨x, x.2.1⟩ : ↥A) = ⟨y, y.2.1⟩ := φ.injective h1
    have h3 : (x : Γ) = (y : Γ) := congrArg (fun w : ↥A => (w : Γ)) h2
    exact Subtype.ext h3
  exact isCyclic_of_injective f hf

theorem torus_two_fix {Γ : Type} [Group Γ] [Finite Γ] (A : Subgroup Γ) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (φ : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) F) {zb a f : Γ}
    (hzA : zb ∈ A) (haA : a ∈ A) (hz : orderOf zb = 2) (hc : ∀ g : Γ, g * zb = zb * g)
    (haz : a * a = zb) (hfA : ∀ x ∈ A, f * x * f⁻¹ ∈ A) (hfa : f * a * f⁻¹ = a) {r : ℕ} (hr : Odd r)
    (hfr : f ^ r = 1) {x : Γ} (hxA : x ∈ A) (hxa : x * a = a * x) {m : ℕ} (hxm : x ^ 2 ^ m = 1) :
    f * x * f⁻¹ = x := by
  have hcyc := sl2_cent_cyclic_sub A hodd φ hzA haA hz hc haz
  have hfa' : f⁻¹ * a * f = a := by
    calc f⁻¹ * a * f = f⁻¹ * (f * a * f⁻¹) * f := by rw [hfa]
      _ = a := by group
  refine conj_eq_of_cyclic_two hcyc ?_ hr hfr ⟨hxA, mem_centralizer_singleton_iff.2 hxa⟩ hxm
  intro y hy
  refine ⟨hfA y hy.1, mem_centralizer_singleton_iff.2 ?_⟩
  have hya : y * a = a * y := mem_centralizer_singleton_iff.1 hy.2
  calc f * y * f⁻¹ * a = f * y * (f⁻¹ * a * f) * f⁻¹ := by group
    _ = f * (y * a) * f⁻¹ := by rw [hfa']; group
    _ = f * (a * y) * f⁻¹ := by rw [hya]
    _ = (f * a * f⁻¹) * (f * y * f⁻¹) := by group
    _ = a * (f * y * f⁻¹) := by rw [hfa]

end Abstract

section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem eq_one_of_piC_eq_one {d : ↥(Cz z)} (hd : piC z d = 1) {a : ℕ} (hda : d ^ 2 ^ a = 1) : d = 1 := by
  have hdk : d ∈ pPrimeCore 2 ↥(Cz z) := (QuotientGroup.eq_one_iff d).1 hd
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cz z))) := TwoThin.odd_card_pPrimeCore _
  have h1 : orderOf d ∣ Nat.card ↥(pPrimeCore 2 ↥(Cz z)) := Subgroup.orderOf_dvd_natCard _ hdk
  have h2 : orderOf d ∣ Nat.gcd (Nat.card ↥(pPrimeCore 2 ↥(Cz z))) (2 ^ a) :=
    Nat.dvd_gcd h1 (orderOf_dvd_of_pow_eq_one hda)
  rw [((Nat.coprime_two_right.2 hodd).pow_right a).gcd_eq_one, Nat.dvd_one] at h2
  exact orderOf_eq_one_iff.1 h2

theorem conj_a₁_cases (hII : II4_4_4_center) (h44 : II4_44) (hf : Fused8 G z S K₁ K₂)
    {a₁ a₂ g : CentralizerBar z} (ha₁ : a₁ ∈ imgBar z K₁) (ha₂ : a₂ ∈ imgBar z K₂)
    (hg₁ : g * a₁ * g⁻¹ ∈ imgBar z K₁) (hg₂ : g * a₂ * g⁻¹ ∈ imgBar z K₂)
    (hgu : g * (a₁ * a₂) = (a₁ * a₂) * g) :
    g * a₁ * g⁻¹ = a₁ ∨ g * a₁ * g⁻¹ = piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ * a₁ := by
  have hcomm := imgBar_comm hII hf
  have hcard := imgBar_inf_card hII h44 hf
  obtain ⟨hzbmem, hzbne⟩ := zbar_facts hII hf
  set zb : CentralizerBar z := piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ with hzb
  set d : CentralizerBar z := g * a₁ * g⁻¹ * a₁⁻¹ with hd
  have hprod : (g * a₁ * g⁻¹) * (g * a₂ * g⁻¹) = a₁ * a₂ := by
    calc (g * a₁ * g⁻¹) * (g * a₂ * g⁻¹) = g * (a₁ * a₂) * g⁻¹ := by group
      _ = a₁ * a₂ := by rw [hgu]; group
  have hd₁ : d ∈ imgBar z K₁ := mul_mem hg₁ (inv_mem ha₁)
  have hd₂ : d ∈ imgBar z K₂ := by
    have e : d = a₂ * (g * a₂ * g⁻¹)⁻¹ := by
      have h1 : g * a₁ * g⁻¹ = a₁ * a₂ * (g * a₂ * g⁻¹)⁻¹ := eq_mul_inv_of_mul_eq hprod
      have h2 : a₁ * (a₂ * (g * a₂ * g⁻¹)⁻¹) = (a₂ * (g * a₂ * g⁻¹)⁻¹) * a₁ :=
        (hcomm a₁ ha₁ _ (mul_mem ha₂ (inv_mem hg₂)))
      calc d = g * a₁ * g⁻¹ * a₁⁻¹ := rfl
        _ = a₁ * (a₂ * (g * a₂ * g⁻¹)⁻¹) * a₁⁻¹ := by rw [h1]; group
        _ = a₂ * (g * a₂ * g⁻¹)⁻¹ := by rw [h2]; group
    rw [e]
    exact mul_mem ha₂ (inv_mem hg₂)
  have hzbord : orderOf zb = 2 := by
    have hz2 : zb * zb = 1 := by
      rw [hzb, ← map_mul]
      have : (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ * ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ :
          ↥(Cz z)) = 1 := Subtype.ext hf.z_sq
      rw [this, map_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hzbne
  have heq : zpowers zb = imgBar z K₁ ⊓ imgBar z K₂ :=
    Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hzbmem) (by rw [hcard, Nat.card_zpowers, hzbord])
  have hdz : d ∈ zpowers zb := by rw [heq]; exact ⟨hd₁, hd₂⟩
  obtain ⟨k, hk0⟩ := hdz
  have hk : zb ^ k = d := hk0
  have hk' : zb ^ k = zb ^ (k % 2) := by
    rw [← zpow_mod_orderOf zb k, hzbord]
    norm_num
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : d = 1 := by rw [← hk, hk', h, zpow_zero]
    calc g * a₁ * g⁻¹ = d * a₁ := by rw [hd]; group
      _ = a₁ := by rw [this, one_mul]
  · right
    have : d = zb := by rw [← hk, hk', h, zpow_one]
    calc g * a₁ * g⁻¹ = d * a₁ := by rw [hd]; group
      _ = zb * a₁ := by rw [this]

theorem odd_centralizes_W (hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hFS : FStar_C) (hf : Fused8 G z S K₁ K₂) {U : Subgroup G} {k₁ k₂ : G} (hzU : z ∈ U)
    (huU : k₁ * k₂ ∈ U) (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂) (hk₁sq : k₁ * k₁ = z) (hk₂sq : k₂ * k₂ = z)
    {c : G} (hcU : c ∈ centralizer (U : Set G)) (hcW : c ∈ normalizer (Wsub S U : Set G))
    (hco : Odd (orderOf c)) :
    ∀ w ∈ Wsub S U, c * w = w * c := by
  classical
  have hM := hf.m4 hII
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hSC : S ≤ Cz z := hf.S_le_C hII
  have hzC : z ∈ Cz z := mem_centralizer_singleton_iff.2 rfl
  have hDC : centralizer (U : Set G) ≤ Cz z := by
    intro g hg
    rw [mem_centralizer_iff] at hg ⊢
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hg z hzU
  have hcC : c ∈ Cz z := hDC hcU
  have hWS : Wsub S U ≤ S := inf_le_left
  have hSp : IsPGroup 2 ↥S := hf.S_pgroup hII
  have hW2 : ∀ w ∈ Wsub S U, ∃ a : ℕ, w ^ 2 ^ a = 1 := by
    intro w hw
    obtain ⟨a, ha⟩ := hSp ⟨w, hWS hw⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hcWW : ∀ w ∈ Wsub S U, c * w * c⁻¹ ∈ Wsub S U := fun w hw => (mem_normalizer_iff.1 hcW w).1 hw
  obtain ⟨hc₁, hc₂⟩ := Leaf.odd_normalizes_comps hf.std hcC hco
  have hLn : ∀ g ∈ centralizer ({z} : Set G), ∀ l ∈ K₁ ⊔ K₂ ⊔ Oz z, g * l * g⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z :=
    L_norm hII hf.std
  have hL1 : ∀ s ∈ Wsub S U, s ∈ normalizer (K₁ : Set G) → c * s * c⁻¹ * s⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z := by
    intro s hs hs₁
    have hsC : s ∈ Cz z := hSC (hWS hs)
    have hs₂ : s ∈ normalizer (K₂ : Set G) := (IVK.Lifted.std4_normalizer_swap hf.std hsC).1 hs₁
    exact Leaf.comm_mem_of_normalizes h44 h2A7 hII hFS hf.std hf.hQ hcC hsC hc₁ hc₂ hs₁ hs₂
  have hL2 : ∀ s ∈ Wsub S U, c * s * c⁻¹ * s⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z := by
    intro s hs
    by_cases hs₁ : s ∈ normalizer (K₁ : Set G)
    · exact hL1 s hs hs₁
    have hsC : s ∈ Cz z := hSC (hWS hs)
    have hyW : c * s * c⁻¹ * s⁻¹ ∈ Wsub S U := mul_mem (hcWW s hs) (inv_mem hs)
    have hyC : c * s * c⁻¹ * s⁻¹ ∈ Cz z := hSC (hWS hyW)
    have hy₁ : c * s * c⁻¹ * s⁻¹ ∈ normalizer (K₁ : Set G) := by
      have hcK₁ : cmap c K₁ = K₁ := (IVK.Lifted.cmap_eq_iff_normalizer K₁ c).2 hc₁
      have hcK₂ : cmap c K₂ = K₂ := (IVK.Lifted.cmap_eq_iff_normalizer K₂ c).2 hc₂
      have hsK : cmap s K₁ = K₂ ∧ cmap s K₂ = K₁ := by
        rcases IVK.Lifted.std4_perm_cmap hf.std hsC with ⟨h1, -⟩ | h
        · exact absurd ((IVK.Lifted.cmap_eq_iff_normalizer K₁ s).1 h1) hs₁
        · exact h
      have hs'K₁ : cmap s⁻¹ K₁ = K₂ := by rw [← hsK.2, cmap_inv_cancel]
      have hc'K₂ : cmap c⁻¹ K₂ = K₂ := by
        calc cmap c⁻¹ K₂ = cmap c⁻¹ (cmap c K₂) := by rw [hcK₂]
          _ = K₂ := cmap_inv_cancel c K₂
      refine (IVK.Lifted.cmap_eq_iff_normalizer K₁ _).1 ?_
      rw [← cmap_cmap (c * s * c⁻¹) s⁻¹, ← cmap_cmap (c * s) c⁻¹, ← cmap_cmap c s, hs'K₁, hc'K₂,
        hsK.2, hcK₁]
    have hcyL := hL1 _ hyW hy₁
    have hQn : ((K₁ ⊔ K₂ ⊔ Oz z).subgroupOf (Cz z)).Normal := ⟨fun n hn g => hLn g g.2 n hn⟩
    let c' : ↥(Cz z) := ⟨c, hcC⟩
    let s' : ↥(Cz z) := ⟨s, hsC⟩
    let y' : ↥(Cz z) := ⟨c * s * c⁻¹ * s⁻¹, hyC⟩
    let π := QuotientGroup.mk' ((K₁ ⊔ K₂ ⊔ Oz z).subgroupOf (Cz z))
    have hcy' : π c' * π y' = π y' * π c' := by
      have h1 : π (c' * y' * c'⁻¹ * y'⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hcyL
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc π c' * π y' = (π c' * π y' * (π c')⁻¹ * (π y')⁻¹) * π y' * π c' := by group
        _ = π y' * π c' := by rw [h1]; group
    have hs' : π c' * π s' * (π c')⁻¹ = π y' * π s' := by
      have e : c' * s' * c'⁻¹ = y' * s' :=
        Subtype.ext (show c * s * c⁻¹ = c * s * c⁻¹ * s⁻¹ * s by group)
      rw [← map_inv, ← map_mul, ← map_mul, e, map_mul]
    have hck : π c' ^ orderOf c = 1 := by
      rw [← map_pow]
      have : c' ^ orderOf c = 1 := Subtype.ext (by simp [c', pow_orderOf_eq_one])
      rw [this, map_one]
    obtain ⟨a, ha⟩ := hW2 _ hyW
    have hya : π y' ^ 2 ^ a = 1 := by
      rw [← map_pow]
      have : y' ^ 2 ^ a = 1 := Subtype.ext (by simpa [y'] using ha)
      rw [this, map_one]
    exact (QuotientGroup.eq_one_iff y').1 (eq_one_of_conj_eq_mul hcy' hs' hco hck hya)
  obtain ⟨F₁, hF₁, hFin₁, hodd₁, ⟨φ₁⟩⟩ := hf.exists_SL2 h44 (Or.inl rfl) hf.d₁
  obtain ⟨F₂, hF₂, hFin₂, hodd₂, ⟨φ₂⟩⟩ := hf.exists_SL2 h44 (Or.inr rfl) hf.d₂
  have hcomm := imgBar_comm hII hf
  have hcard := imgBar_inf_card hII h44 hf
  obtain ⟨hzbmem, hzbne⟩ := zbar_facts hII hf
  set zb : CentralizerBar z := piC z ⟨z, hzC⟩ with hzb
  set a₁ : CentralizerBar z := piC z ⟨k₁, hK₁C hk₁⟩ with ha₁def
  set a₂ : CentralizerBar z := piC z ⟨k₂, hK₂C hk₂⟩ with ha₂def
  set cb : CentralizerBar z := piC z ⟨c, hcC⟩ with hcbdef
  have hzb2 : zb * zb = 1 := by
    rw [hzb, ← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Cz z)) = 1 := Subtype.ext hf.z_sq
    rw [this, map_one]
  have hzbord : orderOf zb = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzb2) hzbne
  have hzbc : ∀ g : CentralizerBar z, g * zb = zb * g := by
    intro g
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective g
    show piC z d * piC z ⟨z, hzC⟩ = piC z ⟨z, hzC⟩ * piC z d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 d.2)
  have hinf : ∀ d ∈ imgBar z K₁ ⊓ imgBar z K₂, d * d = 1 := by
    intro d hd
    have h1 : (⟨d, hd⟩ : ↥(imgBar z K₁ ⊓ imgBar z K₂)) ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥(imgBar z K₁ ⊓ imgBar z K₂)) (x := ⟨d, hd⟩)
      rwa [hcard] at this
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have ha₁ : a₁ ∈ imgBar z K₁ := piC_mem_imgBar hK₁C hk₁
  have ha₂ : a₂ ∈ imgBar z K₂ := piC_mem_imgBar hK₂C hk₂
  have ha₁sq : a₁ * a₁ = zb := by
    rw [ha₁def, ← map_mul]; congr 1; exact Subtype.ext hk₁sq
  have ha₂sq : a₂ * a₂ = zb := by
    rw [ha₂def, ← map_mul]; congr 1; exact Subtype.ext hk₂sq
  have hcbK : ∀ {K : Subgroup G} (hKC : K ≤ Cz z), c ∈ normalizer (K : Set G) →
      ∀ x ∈ imgBar z K, cb * x * cb⁻¹ ∈ imgBar z K := by
    intro K hKC hcK x hx
    obtain ⟨k, hk, rfl⟩ := (mem_imgBar hKC).1 hx
    have hck : c * k * c⁻¹ ∈ K := (mem_normalizer_iff.1 hcK k).1 hk
    refine (mem_imgBar hKC).2 ⟨c * k * c⁻¹, hck, ?_⟩
    rw [hcbdef, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcbu : cb * (a₁ * a₂) = (a₁ * a₂) * cb := by
    have hcu : (k₁ * k₂) * c = c * (k₁ * k₂) := mem_centralizer_iff.1 hcU (k₁ * k₂) huU
    rw [hcbdef, ha₁def, ha₂def, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcu.symm
  have hcbk : cb ^ orderOf c = 1 := by
    rw [hcbdef, ← map_pow]
    have : (⟨c, hcC⟩ : ↥(Cz z)) ^ orderOf c = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hcba₁ : cb * a₁ * cb⁻¹ = a₁ := by
    rcases conj_a₁_cases hII h44 hf ha₁ ha₂ (hcbK hK₁C hc₁ a₁ ha₁) (hcbK hK₂C hc₂ a₂ ha₂) hcbu with
      h | h
    · exact h
    · exfalso
      have h1 : cb * a₁ * cb⁻¹ = zb * a₁ := h
      exact hzbne (eq_one_of_conj_eq_mul (hzbc cb) h1 hco hcbk (a := 1)
        (by rw [pow_one, sq]; exact hzb2))
  have hcba₂ : cb * a₂ * cb⁻¹ = a₂ := by
    have h1 : cb * (a₁ * a₂) * cb⁻¹ = a₁ * a₂ := by rw [hcbu]; group
    calc cb * a₂ * cb⁻¹ = (cb * a₁ * cb⁻¹)⁻¹ * (cb * (a₁ * a₂) * cb⁻¹) := by group
      _ = a₂ := by rw [hcba₁, h1]; group
  have hfix0 : ∀ v ∈ imgBar z K₁ ⊔ imgBar z K₂, v * a₁ = a₁ * v → v * (a₁ * a₂) = (a₁ * a₂) * v →
      ∀ m : ℕ, v ^ 2 ^ m = 1 → cb * v * cb⁻¹ = v := by
    intro v hv hva₁ hvu m hvm
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Basic.mem_sup_of_commute' hcomm hv
    have hx₂a₁ : x₂ * a₁ = a₁ * x₂ := (hcomm a₁ ha₁ x₂ hx₂).symm
    have hx₁a₂ : x₁ * a₂ = a₂ * x₁ := hcomm x₁ hx₁ a₂ ha₂
    have hx₁a : x₁ * a₁ = a₁ * x₁ := by
      have h1 : x₁ * a₁ * x₂ = a₁ * x₁ * x₂ := by
        calc x₁ * a₁ * x₂ = x₁ * (a₁ * x₂) := by group
          _ = x₁ * (x₂ * a₁) := by rw [hx₂a₁]
          _ = x₁ * x₂ * a₁ := by group
          _ = a₁ * (x₁ * x₂) := hva₁
          _ = a₁ * x₁ * x₂ := by group
      exact mul_right_cancel h1
    have hva₂ : x₁ * x₂ * a₂ = a₂ * (x₁ * x₂) := by
      have h1 : a₁⁻¹ * (x₁ * x₂) = (x₁ * x₂) * a₁⁻¹ := by
        calc a₁⁻¹ * (x₁ * x₂) = a₁⁻¹ * (x₁ * x₂ * a₁) * a₁⁻¹ := by group
          _ = a₁⁻¹ * (a₁ * (x₁ * x₂)) * a₁⁻¹ := by rw [hva₁]
          _ = (x₁ * x₂) * a₁⁻¹ := by group
      calc x₁ * x₂ * a₂ = x₁ * x₂ * (a₁⁻¹ * (a₁ * a₂)) := by group
        _ = (x₁ * x₂ * a₁⁻¹) * (a₁ * a₂) := by group
        _ = a₁⁻¹ * (x₁ * x₂) * (a₁ * a₂) := by rw [h1]
        _ = a₁⁻¹ * ((x₁ * x₂) * (a₁ * a₂)) := by group
        _ = a₁⁻¹ * ((a₁ * a₂) * (x₁ * x₂)) := by rw [hvu]
        _ = a₂ * (x₁ * x₂) := by group
    have hx₂a : x₂ * a₂ = a₂ * x₂ := by
      have h1 : x₁ * (x₂ * a₂) = x₁ * (a₂ * x₂) := by
        calc x₁ * (x₂ * a₂) = x₁ * x₂ * a₂ := by group
          _ = a₂ * (x₁ * x₂) := hva₂
          _ = (a₂ * x₁) * x₂ := by group
          _ = (x₁ * a₂) * x₂ := by rw [hx₁a₂]
          _ = x₁ * (a₂ * x₂) := by group
      exact mul_left_cancel h1
    have hc12 : Commute x₁ x₂ := hcomm x₁ hx₁ x₂ hx₂
    have hpow : x₁ ^ 2 ^ m * x₂ ^ 2 ^ m = 1 := by rw [← hc12.mul_pow]; exact hvm
    have hd : x₁ ^ 2 ^ m ∈ imgBar z K₁ ⊓ imgBar z K₂ := by
      have h1 : x₁ ^ 2 ^ m = (x₂ ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      refine Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hx₁ _, ?_⟩
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hx₂ _)
    have hx₁m : x₁ ^ 2 ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, sq]; exact hinf _ hd
    have hx₂m : x₂ ^ 2 ^ (m + 1) = 1 := by
      have : x₂ ^ 2 ^ m = (x₁ ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [pow_succ, pow_mul, sq, this, ← mul_inv_rev, hinf _ hd, inv_one]
    have hf₁ : cb * x₁ * cb⁻¹ = x₁ :=
      torus_two_fix (imgBar z K₁) hodd₁ φ₁ hzbmem.1 ha₁ hzbord hzbc ha₁sq (hcbK hK₁C hc₁) hcba₁ hco
        hcbk hx₁ hx₁a hx₁m
    have hf₂ : cb * x₂ * cb⁻¹ = x₂ :=
      torus_two_fix (imgBar z K₂) hodd₂ φ₂ hzbmem.2 ha₂ hzbord hzbc ha₂sq (hcbK hK₂C hc₂) hcba₂ hco
        hcbk hx₂ hx₂a hx₂m
    calc cb * (x₁ * x₂) * cb⁻¹ = (cb * x₁ * cb⁻¹) * (cb * x₂ * cb⁻¹) := by group
      _ = x₁ * x₂ := by rw [hf₁, hf₂]
  have hvK₁ : ∀ v ∈ imgBar z K₁ ⊔ imgBar z K₂, ∀ x ∈ imgBar z K₁, v * x * v⁻¹ ∈ imgBar z K₁ := by
    intro v hv x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Basic.mem_sup_of_commute' hcomm hv
    have e : x₁ * x₂ * x * (x₁ * x₂)⁻¹ = x₁ * x * x₁⁻¹ := by
      have h1 : x₂ * x = x * x₂ := (hcomm x hx x₂ hx₂).symm
      calc x₁ * x₂ * x * (x₁ * x₂)⁻¹ = x₁ * (x₂ * x) * x₂⁻¹ * x₁⁻¹ := by group
        _ = x₁ * x * x₁⁻¹ := by rw [h1]; group
    rw [e]
    exact mul_mem (mul_mem hx₁ hx) (inv_mem hx₁)
  have hvK₂ : ∀ v ∈ imgBar z K₁ ⊔ imgBar z K₂, ∀ x ∈ imgBar z K₂, v * x * v⁻¹ ∈ imgBar z K₂ := by
    intro v hv x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Basic.mem_sup_of_commute' hcomm hv
    have e : x₁ * x₂ * x * (x₁ * x₂)⁻¹ = x₂ * x * x₂⁻¹ := by
      have h1 : x₁ * (x₂ * x * x₂⁻¹) = (x₂ * x * x₂⁻¹) * x₁ :=
        hcomm x₁ hx₁ _ (mul_mem (mul_mem hx₂ hx) (inv_mem hx₂))
      calc x₁ * x₂ * x * (x₁ * x₂)⁻¹ = x₁ * (x₂ * x * x₂⁻¹) * x₁⁻¹ := by group
        _ = x₂ * x * x₂⁻¹ := by rw [h1]; group
    rw [e]
    exact mul_mem (mul_mem hx₂ hx) (inv_mem hx₂)
  have hbar : ∀ w (hw : w ∈ Wsub S U), w ∈ K₁ ⊔ K₂ ⊔ Oz z →
      piC z ⟨w, hSC (hWS hw)⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
    intro w hw hwL
    rw [← hf.map_L hII]
    exact ⟨⟨w, hSC (hWS hw)⟩, hwL, rfl⟩
  have hbaru : ∀ w (hw : w ∈ Wsub S U), piC z ⟨w, hSC (hWS hw)⟩ * (a₁ * a₂) =
      (a₁ * a₂) * piC z ⟨w, hSC (hWS hw)⟩ := by
    intro w hw
    have hwu : (k₁ * k₂) * w = w * (k₁ * k₂) := mem_centralizer_iff.1 hw.2 (k₁ * k₂) huU
    rw [ha₁def, ha₂def, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwu.symm
  have hbar2 : ∀ w (hw : w ∈ Wsub S U), ∃ m : ℕ, piC z ⟨w, hSC (hWS hw)⟩ ^ 2 ^ m = 1 := by
    intro w hw
    obtain ⟨m, hm⟩ := hW2 w hw
    refine ⟨m, ?_⟩
    rw [← map_pow]
    have : (⟨w, hSC (hWS hw)⟩ : ↥(Cz z)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [this, map_one]
  have hfixL : ∀ w (hw : w ∈ Wsub S U), w ∈ K₁ ⊔ K₂ ⊔ Oz z →
      cb * piC z ⟨w, hSC (hWS hw)⟩ * cb⁻¹ = piC z ⟨w, hSC (hWS hw)⟩ := by
    intro w hw hwL
    set wb := piC z ⟨w, hSC (hWS hw)⟩ with hwb
    obtain ⟨m, hm⟩ := hbar2 w hw
    by_cases hwa : wb * a₁ = a₁ * wb
    · exact hfix0 wb (hbar w hw hwL) hwa (hbaru w hw) m hm
    have hwa' : wb * a₁ * wb⁻¹ = zb * a₁ := by
      rcases conj_a₁_cases hII h44 hf ha₁ ha₂ (hvK₁ wb (hbar w hw hwL) a₁ ha₁)
        (hvK₂ wb (hbar w hw hwL) a₂ ha₂) (hbaru w hw) with h | h
      · exfalso
        apply hwa
        calc wb * a₁ = (wb * a₁ * wb⁻¹) * wb := by group
          _ = a₁ * wb := by rw [h]
      · exact h
    have hyW : c * w * c⁻¹ * w⁻¹ ∈ Wsub S U := mul_mem (hcWW w hw) (inv_mem hw)
    have hyL : c * w * c⁻¹ * w⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z :=
      mul_mem (hLn c hcC w hwL) (inv_mem hwL)
    have hyb : piC z ⟨c * w * c⁻¹ * w⁻¹, hSC (hWS hyW)⟩ = cb * wb * cb⁻¹ * wb⁻¹ := by
      rw [hcbdef, hwb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    set yb := piC z ⟨c * w * c⁻¹ * w⁻¹, hSC (hWS hyW)⟩ with hybdef
    have hcba₁' : cb⁻¹ * a₁ * cb = a₁ := by
      calc cb⁻¹ * a₁ * cb = cb⁻¹ * (cb * a₁ * cb⁻¹) * cb := by rw [hcba₁]
        _ = a₁ := by group
    have hwa'' : wb⁻¹ * a₁ * wb = zb * a₁ := by
      have h1 : a₁ = wb⁻¹ * (zb * a₁) * wb := by rw [← hwa']; group
      have h2 : wb⁻¹ * (zb * a₁) * wb = zb * (wb⁻¹ * a₁ * wb) := by
        rw [show wb⁻¹ * (zb * a₁) * wb = (wb⁻¹ * zb) * a₁ * wb by group, hzbc wb⁻¹]; group
      have h3 : a₁ = zb * (wb⁻¹ * a₁ * wb) := h1.trans h2
      calc wb⁻¹ * a₁ * wb = (zb * zb) * (wb⁻¹ * a₁ * wb) := by rw [hzb2, one_mul]
        _ = zb * (zb * (wb⁻¹ * a₁ * wb)) := by group
        _ = zb * a₁ := by rw [← h3]
    have hya : yb * a₁ = a₁ * yb := by
      have h1 : yb * a₁ * yb⁻¹ = a₁ := by
        rw [hyb]
        calc cb * wb * cb⁻¹ * wb⁻¹ * a₁ * (cb * wb * cb⁻¹ * wb⁻¹)⁻¹
            = cb * wb * cb⁻¹ * (wb⁻¹ * a₁ * wb) * cb * wb⁻¹ * cb⁻¹ := by group
          _ = cb * wb * cb⁻¹ * (zb * a₁) * cb * wb⁻¹ * cb⁻¹ := by rw [hwa'']
          _ = zb * (cb * wb * (cb⁻¹ * a₁ * cb) * wb⁻¹ * cb⁻¹) := by
              rw [show cb * wb * cb⁻¹ * (zb * a₁) * cb * wb⁻¹ * cb⁻¹ =
                (cb * wb * cb⁻¹ * zb) * a₁ * cb * wb⁻¹ * cb⁻¹ by group,
                show cb * wb * cb⁻¹ * zb = zb * (cb * wb * cb⁻¹) from hzbc _]
              group
          _ = zb * (cb * (wb * a₁ * wb⁻¹) * cb⁻¹) := by rw [hcba₁']; group
          _ = zb * (cb * (zb * a₁) * cb⁻¹) := by rw [hwa']
          _ = zb * zb * (cb * a₁ * cb⁻¹) := by
              rw [show cb * (zb * a₁) * cb⁻¹ = (cb * zb) * a₁ * cb⁻¹ by group, hzbc cb]; group
          _ = a₁ := by rw [hzb2, hcba₁, one_mul]
      calc yb * a₁ = (yb * a₁ * yb⁻¹) * yb := by group
        _ = a₁ * yb := by rw [h1]
    obtain ⟨my, hmy⟩ := hbar2 _ hyW
    have hcy : cb * yb * cb⁻¹ = yb := hfix0 yb (hbar _ hyW hyL) hya (hbaru _ hyW) my hmy
    have hcy' : cb * yb = yb * cb := by
      calc cb * yb = (cb * yb * cb⁻¹) * cb := by group
        _ = yb * cb := by rw [hcy]
    have hs : cb * wb * cb⁻¹ = yb * wb := by rw [hyb]; group
    have hy1 : yb = 1 := eq_one_of_conj_eq_mul hcy' hs hco hcbk hmy
    rw [hs, hy1, one_mul]
  have hcomL : ∀ w ∈ Wsub S U, w ∈ K₁ ⊔ K₂ ⊔ Oz z → c * w = w * c := by
    intro w hw hwL
    have hdW : c * w * c⁻¹ * w⁻¹ ∈ Wsub S U := mul_mem (hcWW w hw) (inv_mem hw)
    obtain ⟨m, hm⟩ := hW2 _ hdW
    have hd1 : piC z ⟨c * w * c⁻¹ * w⁻¹, hSC (hWS hdW)⟩ = 1 := by
      have h := hfixL w hw hwL
      have e : piC z ⟨c * w * c⁻¹ * w⁻¹, hSC (hWS hdW)⟩ =
          cb * piC z ⟨w, hSC (hWS hw)⟩ * cb⁻¹ * (piC z ⟨w, hSC (hWS hw)⟩)⁻¹ := by
        rw [hcbdef, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [e, h, mul_inv_cancel]
    have hd2 : (⟨c * w * c⁻¹ * w⁻¹, hSC (hWS hdW)⟩ : ↥(Cz z)) = 1 :=
      eq_one_of_piC_eq_one hd1 (a := m) (Subtype.ext (by simpa using hm))
    have hd3 : c * w * c⁻¹ * w⁻¹ = 1 := congrArg Subtype.val hd2
    calc c * w = (c * w * c⁻¹ * w⁻¹) * w * c := by group
      _ = w * c := by rw [hd3, one_mul]
  intro w hw
  have hyW : c * w * c⁻¹ * w⁻¹ ∈ Wsub S U := mul_mem (hcWW w hw) (inv_mem hw)
  have hcy : c * (c * w * c⁻¹ * w⁻¹) = (c * w * c⁻¹ * w⁻¹) * c := hcomL _ hyW (hL2 w hw)
  obtain ⟨m, hm⟩ := hW2 _ hyW
  have hs : c * w * c⁻¹ = (c * w * c⁻¹ * w⁻¹) * w := by group
  have hy1 := eq_one_of_conj_eq_mul hcy hs hco (pow_orderOf_eq_one c) hm
  calc c * w = (c * w * c⁻¹ * w⁻¹) * w * c := by group
    _ = w * c := by rw [hy1, one_mul]

end Ctx

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1
