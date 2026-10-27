module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModFacXa
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

variable {G : Type} [Group G]

theorem sec12S8Mod_facX_perm {V X : Subgroup G} (h : IsNatModA5 V ⊥ X) :
    ∃ φ : (Fin 5 → ZMod 2) → G, X ≤ normalizer (V : Set G) ∧
      (∀ v, IsEvenVec v → φ v ∈ V) ∧
      (∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w) ∧
      (∀ v, IsEvenVec v → φ v = 1 → v = 0) ∧
      (∀ x ∈ V, ∃ v, IsEvenVec v ∧ φ v = x) ∧
      (∀ x ∈ X, ∃ σ ∈ alternatingGroup (Fin 5),
        ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) ∧
      (∀ σ ∈ alternatingGroup (Fin 5), ∃ x ∈ X,
        ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) := by
  obtain ⟨φ, hmod⟩ := h
  unfold IsPermModuleMod at hmod
  obtain ⟨_, _, h3, _, h5, h6, h7, h8, h9, h10⟩ := hmod
  refine ⟨φ, h3, h5, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (h6 v w hv hw))).symm
  · intro v hv hφv
    exact Set.mem_singleton_iff.mp ((h7 v hv).mp (Subgroup.mem_bot.mpr hφv))
  · intro x hx
    obtain ⟨v, hv, hbv⟩ := h8 x hx
    exact ⟨v, hv, inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbv)⟩
  · intro x hx
    obtain ⟨σ, hσ, hσv⟩ := h9 x hx
    exact ⟨σ, hσ, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hσv v hv))⟩
  · intro σ hσ
    obtain ⟨x, hx, hxv⟩ := h10 σ hσ
    exact ⟨x, hx, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hxv v hv))⟩

theorem sec12S8Mod_facX_five (σ : Equiv.Perm (Fin 5)) (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1)
    (v : Fin 5 → ZMod 2) (hv : IsEvenVec v) (hfix : permVec σ v = v) : v = 0 :=
  s8FacX_five σ h5 h1 v hv hfix

theorem sec12S8Mod_facX_three (σ : Equiv.Perm (Fin 5)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec σ v = v} = 4 := by
  exact s8FacX_three σ h3 h1

theorem sec12S8Mod_facX_faithful {V X : Subgroup G}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) (h : IsNatModA5 V ⊥ X) {x : G}
    (hx : x ∈ X) (hxv : ∀ v ∈ V, x * v * x⁻¹ = v) : x = 1 := by
  obtain ⟨φ, hXnorm, hφV, hφhom, hφker, hφsurj, hact, hocc⟩ := sec12S8Mod_facX_perm h
  have hφ0 : φ 0 = 1 := s8FacX_phi_zero hφhom
  have hφinj : ∀ {v w : Fin 5 → ZMod 2}, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w :=
    fun hv hw hh => s8FacX_phi_injective hφhom hφker hφ0 hv hw hh
  haveI : IsSimpleGroup ↥X := by
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    exact MulEquiv.isSimpleGroup hA5.some
  let K : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G)
  have hKnormal : (K.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (show K ≤ X from inf_le_left)]
    intro k h hkK hhX
    rw [Subgroup.mem_inf] at hkK ⊢
    refine ⟨X.mul_mem (X.mul_mem hhX hkK.1) (X.inv_mem hhX), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hkK ⊢
    intro v hv
    have hv' : h⁻¹ * v * h ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hXnorm (X.inv_mem hhX)) v).mp hv
      simpa using this
    calc v * (h * k * h⁻¹) = h * ((h⁻¹ * v * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * v * h)) * h⁻¹ := by rw [hkK.2 _ hv']
      _ = (h * k * h⁻¹) * v := by group
  have hKtop_ne : K.subgroupOf X ≠ ⊤ := by
    intro htop
    obtain ⟨σ0, hσ0A, hσ0move⟩ := s8FacX_exists_alt_moves
    obtain ⟨x0, hx0X, hx0act⟩ := hocc σ0 hσ0A
    have hx0notK : x0 ∉ K := by
      intro hx0K
      have hmem : φ s8FacX_v0 ∈ V := hφV s8FacX_v0 s8FacX_isEvenVec_v0
      have hc := Subgroup.mem_centralizer_iff.mp hx0K.2 (φ s8FacX_v0) hmem
      have hfix : x0 * φ s8FacX_v0 * x0⁻¹ = φ s8FacX_v0 := by
        show (x0 * φ s8FacX_v0) * x0⁻¹ = φ s8FacX_v0
        rw [show x0 * φ s8FacX_v0 = φ s8FacX_v0 * x0 from hc.symm]
        group
      have h2 := hx0act s8FacX_v0 s8FacX_isEvenVec_v0
      have heq : φ (permVec σ0 s8FacX_v0) = φ s8FacX_v0 := h2.symm.trans hfix
      exact hσ0move
        (hφinj (s8FacX_isEvenVec_permVec σ0 s8FacX_v0 s8FacX_isEvenVec_v0) s8FacX_isEvenVec_v0 heq)
    have : (⟨x0, hx0X⟩ : ↥X) ∈ K.subgroupOf X := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at this
    exact hx0notK this
  haveI : (K.subgroupOf X).Normal := hKnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.subgroupOf X) with hbot | htop
  · have hxK : (⟨x, hx⟩ : ↥X) ∈ K.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (mul_inv_eq_iff_eq_mul.mp (hxv v hv)).symm
    rw [hbot] at hxK
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxK)
  · exact absurd htop hKtop_ne

theorem sec12S8Mod_facX_one {V X : Subgroup G}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) (h : IsNatModA5 V ⊥ X) :
    (∀ x ∈ X, orderOf x = 5 → ∀ v ∈ V, x * v * x⁻¹ = v → v = 1) ∧
      ∀ x ∈ X, orderOf x = 3 → Nat.card {v : ↥V // x * (v : G) * x⁻¹ = v} = 4 := by
  obtain ⟨φ, _, hφV, hφhom, hφker, hφsurj, hact, hocc⟩ := sec12S8Mod_facX_perm h
  have hφ0 : φ 0 = 1 := s8FacX_phi_zero hφhom
  have hφinj : ∀ {v w : Fin 5 → ZMod 2}, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w :=
    fun hv hw hh => s8FacX_phi_injective hφhom hφker hφ0 hv hw hh
  have hne : ∀ (x : G), x ∈ X → (orderOf x = 5 ∨ orderOf x = 3) → x ≠ 1 := by
    intro x _ hxord hx1
    rw [hx1, orderOf_one] at hxord
    omega
  have hsigma_ne : ∀ (x : G) (hx : x ∈ X) (σ : Equiv.Perm (Fin 5)),
      (∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) → σ = 1 → x = 1 := by
    intro x hx σ hσact hσ1
    apply sec12S8Mod_facX_faithful hA5 h hx
    intro y hy
    obtain ⟨w, hw, hwv⟩ := hφsurj y hy
    have h := hσact w hw
    rw [hσ1, s8FacX_permVec_one] at h
    rw [← hwv]
    exact h
  constructor
  · intro x hx hxord v hv hfix
    obtain ⟨σ, _, hσact⟩ := hact x hx
    have hxpow : x ^ 5 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hσ5 : σ ^ 5 = 1 := by
      apply s8FacX_permVec_injective
      intro w hw
      have h := s8FacX_conj_pow_phi hσact 5 w hw
      rw [hxpow, one_mul, inv_one, mul_one] at h
      exact (hφinj hw (s8FacX_isEvenVec_permVec (σ ^ 5) w hw) h).symm
    have hσ1 : σ ≠ 1 := fun hs => hne x hx (Or.inl hxord) (hsigma_ne x hx σ hσact hs)
    obtain ⟨w, hw, hwv⟩ := hφsurj v hv
    have hwfix : permVec σ w = w := by
      have h := hσact w hw
      have h' : x * φ w * x⁻¹ = φ w := by rw [← hwv] at hfix; exact hfix
      exact (hφinj hw (s8FacX_isEvenVec_permVec σ w hw) (h'.symm.trans h)).symm
    rw [← hwv, sec12S8Mod_facX_five σ hσ5 hσ1 w hw hwfix, hφ0]
  · intro x hx hxord
    obtain ⟨σ, _, hσact⟩ := hact x hx
    have hxpow : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hσ3 : σ ^ 3 = 1 := by
      apply s8FacX_permVec_injective
      intro w hw
      have h := s8FacX_conj_pow_phi hσact 3 w hw
      rw [hxpow, one_mul, inv_one, mul_one] at h
      exact (hφinj hw (s8FacX_isEvenVec_permVec (σ ^ 3) w hw) h).symm
    have hσ1 : σ ≠ 1 := fun hs => hne x hx (Or.inr hxord) (hsigma_ne x hx σ hσact hs)
    let F : Type := {v : ↥V // x * (v : G) * x⁻¹ = v}
    let G3 : Type := {w : Fin 5 → ZMod 2 // IsEvenVec w ∧ permVec σ w = w}
    have hcard3 : Nat.card G3 = 4 := sec12S8Mod_facX_three σ hσ3 hσ1
    let fwd : G3 → F := fun w =>
      ⟨⟨φ w.1, hφV w.1 w.2.1⟩, by
        have := hσact w.1 w.2.1
        rwa [w.2.2] at this⟩
    have hfwd_inj : Function.Injective fwd := by
      intro w1 w2 h
      have hG : φ w1.1 = φ w2.1 := congrArg (fun z : F => (z.1 : G)) h
      exact Subtype.ext (hφinj w1.2.1 w2.2.1 hG)
    have hfwd_surj : Function.Surjective fwd := by
      intro y
      obtain ⟨w, hw, hwv⟩ := hφsurj (y.1 : G) y.1.2
      have hwfix : permVec σ w = w := by
        have h := hσact w hw
        have hy : x * φ w * x⁻¹ = φ w := by simpa only [← hwv] using y.2
        exact (hφinj hw (s8FacX_isEvenVec_permVec σ w hw) (hy.symm.trans h)).symm
      refine ⟨⟨w, hw, hwfix⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hwv
    change Nat.card F = 4
    calc Nat.card F = Nat.card G3 :=
          (Nat.card_congr (Equiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩)).symm
      _ = 4 := hcard3

theorem sec12S8Mod_facX_prod {V V1 V2 : Subgroup G} (hV : IsElemAb2 V 8) (hsup : V1 ⊔ V2 = V)
    (hinf : V1 ⊓ V2 = ⊥) {x : G} (hx1 : x ∈ normalizer (V1 : Set G))
    (hx2 : x ∈ normalizer (V2 : Set G)) :
    Nat.card {v : ↥V // x * (v : G) * x⁻¹ = v} =
      Nat.card {v : ↥V1 // x * (v : G) * x⁻¹ = v} *
        Nat.card {v : ↥V2 // x * (v : G) * x⁻¹ = v} := by
  have hV1V : V1 ≤ V := hsup ▸ le_sup_left
  have hV2V : V2 ≤ V := hsup ▸ le_sup_right
  haveI hcomm : IsMulCommutative ↥V := hV.1.1
  let f : ↥V1 × ↥V2 → ↥V := fun p =>
    ⟨(p.1 : G) * (p.2 : G), V.mul_mem (hV1V p.1.2) (hV2V p.2.2)⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have hG : (a1 : G) * (b1 : G) = (a2 : G) * (b2 : G) := congrArg Subtype.val h
    obtain ⟨ha, hb⟩ := s8FacX_prod_decomp_unique hinf a1.2 a2.2 b1.2 b2.2 hG
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hf_surj : Function.Surjective f := by
    intro v
    have hvtop : v ∈ (V1.subgroupOf V) ⊔ (V2.subgroupOf V) := by
      rw [← Subgroup.subgroupOf_sup hV1V hV2V, hsup, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top v
    rw [Subgroup.mem_sup_of_normal_right] at hvtop
    obtain ⟨a, ha, b, hb, hab⟩ := hvtop
    exact ⟨(⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩, ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩),
      Subtype.ext (congrArg Subtype.val hab)⟩
  let e : ↥V1 × ↥V2 ≃ ↥V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hfix : ∀ p : ↥V1 × ↥V2,
      ((x * (p.1 : G) * x⁻¹ = (p.1 : G)) ∧ (x * (p.2 : G) * x⁻¹ = (p.2 : G))) ↔
        x * ((e p : ↥V) : G) * x⁻¹ = ((e p : ↥V) : G) := by
    intro p
    have he : ((e p : ↥V) : G) = (p.1 : G) * (p.2 : G) := rfl
    constructor
    · rintro ⟨h1, h2⟩
      calc x * ((e p : ↥V) : G) * x⁻¹ = x * ((p.1 : G) * (p.2 : G)) * x⁻¹ := by rw [he]
        _ = (x * (p.1 : G) * x⁻¹) * (x * (p.2 : G) * x⁻¹) := by group
        _ = (p.1 : G) * (p.2 : G) := by rw [h1, h2]
        _ = ((e p : ↥V) : G) := he.symm
    · intro h
      have h1mem : x * (p.1 : G) * x⁻¹ ∈ V1 :=
        (Subgroup.mem_normalizer_iff.mp hx1 (p.1 : G)).mp p.1.2
      have h2mem : x * (p.2 : G) * x⁻¹ ∈ V2 :=
        (Subgroup.mem_normalizer_iff.mp hx2 (p.2 : G)).mp p.2.2
      have hprod : (x * (p.1 : G) * x⁻¹) * (x * (p.2 : G) * x⁻¹) =
          (p.1 : G) * (p.2 : G) := by
        rw [he] at h
        calc (x * (p.1 : G) * x⁻¹) * (x * (p.2 : G) * x⁻¹)
            = x * ((p.1 : G) * (p.2 : G)) * x⁻¹ := by group
          _ = (p.1 : G) * (p.2 : G) := h
      exact s8FacX_prod_decomp_unique hinf h1mem p.1.2 h2mem p.2.2 hprod
  have hcard :
      Nat.card {p : ↥V1 × ↥V2 //
          (x * (p.1 : G) * x⁻¹ = (p.1 : G)) ∧ (x * (p.2 : G) * x⁻¹ = (p.2 : G))} =
        Nat.card {v : ↥V1 // x * (v : G) * x⁻¹ = v} *
          Nat.card {v : ↥V2 // x * (v : G) * x⁻¹ = v} := by
    calc Nat.card {p : ↥V1 × ↥V2 // (x * (p.1 : G) * x⁻¹ = (p.1 : G)) ∧
            (x * (p.2 : G) * x⁻¹ = (p.2 : G))}
        = Nat.card ({a : ↥V1 // x * (a : G) * x⁻¹ = (a : G)} ×
            {b : ↥V2 // x * (b : G) * x⁻¹ = (b : G)}) :=
          Nat.card_congr (Equiv.subtypeProdEquivProd (α := ↥V1) (β := ↥V2)
            (p := fun a : ↥V1 => x * (a : G) * x⁻¹ = (a : G))
            (q := fun b : ↥V2 => x * (b : G) * x⁻¹ = (b : G)))
      _ = Nat.card {v : ↥V1 // x * (v : G) * x⁻¹ = v} *
            Nat.card {v : ↥V2 // x * (v : G) * x⁻¹ = v} := Nat.card_prod _ _
  rw [← hcard]
  exact (Nat.card_congr (e.subtypeEquiv (fun p => hfix p))).symm

theorem sec12S8Mod_facX {V X V1 V2 : Subgroup G} (hV : IsElemAb2 V 8) (hsup : V1 ⊔ V2 = V)
    (hinf : V1 ⊓ V2 = ⊥) (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hn1 : IsNatModA5 V1 ⊥ X) (hn2 : IsNatModA5 V2 ⊥ X) :
    ∃ g h : MulAut ↥V, g ∈ autIn X V ∧ h ∈ autIn X V ∧ g ^ 5 = 1 ∧
      (∀ v : ↥V, g v = v → v = 1) ∧ h ^ 3 = 1 ∧ h ≠ 1 ∧
      Nat.card {v : ↥V // h v = v} = 16 := by
  obtain ⟨_, hXnorm1, -, -, -, -, -, -⟩ := sec12S8Mod_facX_perm hn1
  obtain ⟨_, hXnorm2, -, -, -, -, -, -⟩ := sec12S8Mod_facX_perm hn2
  haveI : Finite ↥X := Finite.of_injective hA5.some hA5.some.injective
  have hcardX : Nat.card ↥X = 60 := by
    rw [Nat.card_congr hA5.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x5, hx5ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 (by rw [hcardX]; norm_num)
  obtain ⟨x3, hx3ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hcardX]; norm_num)
  let g5 : G := (x5 : G)
  let g3 : G := (x3 : G)
  have hg5mem : g5 ∈ X := x5.2
  have hg3mem : g3 ∈ X := x3.2
  have hg5ord : orderOf g5 = 5 := (Subgroup.orderOf_coe x5).trans hx5ord
  have hg3ord : orderOf g3 = 3 := (Subgroup.orderOf_coe x3).trans hx3ord
  have hg5pow : g5 ^ 5 = 1 := by
    have h : x5 ^ 5 = 1 := by rw [← hx5ord]; exact pow_orderOf_eq_one x5
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hg3pow : g3 ^ 3 = 1 := by
    have h : x3 ^ 3 = 1 := by rw [← hx3ord]; exact pow_orderOf_eq_one x3
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have hXnorm : X ≤ normalizer (V : Set G) := by
    have h12 : X ≤ normalizer (V1 : Set G) ⊓ normalizer (V2 : Set G) := le_inf hXnorm1 hXnorm2
    simpa [hsup] using h12.trans (Subgroup.inf_normalizer_le_normalizer_sup V1 V2)
  let g : MulAut ↥V := V.normalizerMonoidHom ⟨g5, hXnorm hg5mem⟩
  let h : MulAut ↥V := V.normalizerMonoidHom ⟨g3, hXnorm hg3mem⟩
  have hgaut : g ∈ autIn X V := by
    rw [autIn, Subgroup.mem_map]
    exact ⟨⟨g5, hXnorm hg5mem⟩, by rw [Subgroup.mem_subgroupOf]; exact hg5mem, rfl⟩
  have hhaut : h ∈ autIn X V := by
    rw [autIn, Subgroup.mem_map]
    exact ⟨⟨g3, hXnorm hg3mem⟩, by rw [Subgroup.mem_subgroupOf]; exact hg3mem, rfl⟩
  have hgpow : g ^ 5 = 1 := by
    change (V.normalizerMonoidHom ⟨g5, hXnorm hg5mem⟩) ^ 5 = 1
    rw [← map_pow]
    have h5' : (⟨g5, hXnorm hg5mem⟩ : ↥(normalizer (V : Set G))) ^ 5 = 1 := by
      apply Subtype.ext
      simpa using hg5pow
    rw [h5', map_one]
  have hhpow : h ^ 3 = 1 := by
    change (V.normalizerMonoidHom ⟨g3, hXnorm hg3mem⟩) ^ 3 = 1
    rw [← map_pow]
    have h3' : (⟨g3, hXnorm hg3mem⟩ : ↥(normalizer (V : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hg3pow
    rw [h3', map_one]
  have hgfree : ∀ v : ↥V, g v = v → v = 1 := by
    intro v hv
    have hvfix : g5 * (v : G) * g5⁻¹ = (v : G) := by
      have h := congrArg (fun z : ↥V => (z : G)) hv
      rw [show g = V.normalizerMonoidHom ⟨g5, hXnorm hg5mem⟩ from rfl,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      exact h
    have hcardV1 : Nat.card {v : ↥V1 // g5 * (v : G) * g5⁻¹ = v} = 1 := by
      have hfix1 : ∀ v ∈ V1, g5 * v * g5⁻¹ = v → v = 1 :=
        (sec12S8Mod_facX_one hA5 hn1).1 g5 hg5mem hg5ord
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, by simp⟩, fun y => ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hfix1 (y.1 : G) y.1.2 y.2
    have hcardV2 : Nat.card {v : ↥V2 // g5 * (v : G) * g5⁻¹ = v} = 1 := by
      have hfix2 : ∀ v ∈ V2, g5 * v * g5⁻¹ = v → v = 1 :=
        (sec12S8Mod_facX_one hA5 hn2).1 g5 hg5mem hg5ord
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, by simp⟩, fun y => ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hfix2 (y.1 : G) y.1.2 y.2
    have hprod := sec12S8Mod_facX_prod hV hsup hinf (hXnorm1 hg5mem) (hXnorm2 hg5mem)
    rw [hcardV1, hcardV2, mul_one] at hprod
    have hvfix' : g5 * (v : G) * g5⁻¹ = v := hvfix
    obtain ⟨w, hw⟩ := Nat.card_eq_one_iff_exists.mp hprod
    have h1 : (⟨v, hvfix'⟩ : {v : ↥V // g5 * (v : G) * g5⁻¹ = v}) = w := hw _
    have h2 : (⟨1, by simp⟩ : {v : ↥V // g5 * (v : G) * g5⁻¹ = v}) = w := hw _
    exact Subtype.ext_iff.mp (h1.trans h2.symm)
  have hcardH : Nat.card {v : ↥V // h v = v} = 16 := by
    have hcardV3 : Nat.card {v : ↥V // g3 * (v : G) * g3⁻¹ = v} = 16 := by
      have h1 := (sec12S8Mod_facX_one hA5 hn1).2 g3 hg3mem hg3ord
      have h2 := (sec12S8Mod_facX_one hA5 hn2).2 g3 hg3mem hg3ord
      have hp := sec12S8Mod_facX_prod hV hsup hinf (hXnorm1 hg3mem) (hXnorm2 hg3mem)
      rw [h1, h2] at hp
      norm_num at hp
      exact hp
    have hp : Nat.card {v : ↥V // h v = v} =
        Nat.card {v : ↥V // g3 * (v : G) * g3⁻¹ = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => by
        constructor
        · intro hv
          have hh := congrArg (fun z : ↥V => (z : G)) hv
          rw [show h = V.normalizerMonoidHom ⟨g3, hXnorm hg3mem⟩ from rfl,
            Subgroup.normalizerMonoidHom_apply_apply_coe] at hh
          exact hh
        · intro hv
          apply Subtype.ext
          rw [show h = V.normalizerMonoidHom ⟨g3, hXnorm hg3mem⟩ from rfl,
            Subgroup.normalizerMonoidHom_apply_apply_coe]
          exact hv))
    rw [hp, hcardV3]
  have hne : h ≠ 1 := by
    intro h1
    have hcard_eq : Nat.card {v : ↥V // h v = v} = Nat.card ↥V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => by rw [h1]; rfl))
    have hVcard : Nat.card ↥V = 256 := by
      rw [hV.2]
      norm_num
    rw [hcardH, hVcard] at hcard_eq
    norm_num at hcard_eq
  exact ⟨g, h, hgaut, hhaut, hgpow, hgfree, hhpow, hne, hcardH⟩

end CFSG.OddStandard.SmallF3.Omega
