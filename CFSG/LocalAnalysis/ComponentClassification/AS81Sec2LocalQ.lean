module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2QUniq

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

variable {G : Type} [Group G] {S Z H : Subgroup G} {x t z : G}

theorem Coord.eq_fixS (C : Coord S Z H) (hS : Special S Z) {P N : Subgroup G} (hPH : P ≤ H)
    (hPS : P ≤ normalizer (S : Set G)) (hNS : N ≤ S)
    (hN : {a | a ∈ P ⊔ S ∧ ∀ b ∈ P ⊔ S, a⁻¹ * b⁻¹ * a * b ∈ Z} = (N : Set G)) :
    N = C.fixS hS ((P.subgroupOf H).map C.φ) := by
  ext a
  constructor
  · intro ha
    have ha' : a ∈ {a | a ∈ P ⊔ S ∧ ∀ b ∈ P ⊔ S, a⁻¹ * b⁻¹ * a * b ∈ Z} := by
      rw [hN]
      exact ha
    refine ⟨hNS ha, fun σ hσ => ?_⟩
    obtain ⟨⟨p, hpH⟩, hp, rfl⟩ := hσ
    have hp' : p ∈ P := hp
    have hpa : p * a * p⁻¹ ∈ S := (mem_normalizer_iff.mp (hPS hp') a).mp (hNS ha)
    rw [← C.Ψ_conj hS ⟨p, hpH⟩ (hNS ha)]
    show C.Ψ (p * a * p⁻¹) = C.Ψ a
    rw [C.Ψ_eq_iff hS hpa (hNS ha)]
    have h1 := ha'.2 p⁻¹ (mem_sup_left (inv_mem hp'))
    have e : p * a * p⁻¹ * a⁻¹ = a * (a⁻¹ * p⁻¹⁻¹ * a * p⁻¹) * a⁻¹ := by group
    rw [e, hS.conj_Z h1 (hNS ha)]
    exact h1
  · intro ha
    rw [← SetLike.mem_coe, ← hN]
    refine ⟨mem_sup_right ha.1, fun b hb => ?_⟩
    have hmul : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right P S hPS
    have hb' : b ∈ ((P ⊔ S : Subgroup G) : Set G) := hb
    rw [hmul] at hb'
    obtain ⟨p, hp, s', hs', rfl⟩ := hb'
    have hm : p⁻¹ * a * p ∈ S := by
      have := (mem_normalizer_iff.mp (hPS (inv_mem hp)) a).mp ha.1
      simpa using this
    have hpinv : C.Ψ (p⁻¹ * a * p) = C.Ψ a := by
      have h1 := C.Ψ_conj hS ⟨p⁻¹, hPH (inv_mem hp)⟩ ha.1
      rw [inv_inv] at h1
      rw [h1]
      exact ha.2 _ ⟨⟨p⁻¹, hPH (inv_mem hp)⟩, inv_mem hp, rfl⟩
    have h2 : a⁻¹ * (p⁻¹ * a * p) ∈ Z := by
      have h3 := (C.Ψ_eq_iff hS hm ha.1).mp hpinv
      have e : a⁻¹ * (p⁻¹ * a * p) = a⁻¹ * ((p⁻¹ * a * p) * a⁻¹) * a := by group
      rw [e, hS.conj_Z' h3 ha.1]
      exact h3
    have h4 : (p⁻¹ * a * p)⁻¹ * s'⁻¹ * (p⁻¹ * a * p) * s' ∈ Z := by
      have := hS.comm_mem (inv_mem hm) (inv_mem hs')
      simpa using this
    have e : a⁻¹ * (p * s')⁻¹ * a * (p * s') =
        (a⁻¹ * (p⁻¹ * a * p)) * ((p⁻¹ * a * p)⁻¹ * s'⁻¹ * (p⁻¹ * a * p) * s') := by group
    rw [e]
    exact Z.mul_mem h2 h4

theorem Coord.card_map_φ (C : Coord S Z H) {P : Subgroup G} (hPH : P ≤ H) :
    Nat.card ((P.subgroupOf H).map C.φ) = S.relIndex P := by
  rw [← Subgroup.relIndex_ker, C.ker, Subgroup.relIndex_subgroupOf hPH]

theorem eq_one_of_conj_x (hS : Special S Z) (hx : XData S Z x) {s : G} (hs : s ∈ S)
    (hxs : x * s * x⁻¹ = s) : s = 1 := by
  have h1 : x⁻¹ * s * x = s := by
    calc x⁻¹ * s * x = x⁻¹ * (x * s * x⁻¹) * x := by rw [hxs]
      _ = s := by group
  have h2 : x⁻¹ * x⁻¹ * s * x * x = s := by
    calc x⁻¹ * x⁻¹ * s * x * x = x⁻¹ * (x⁻¹ * s * x) * x := by group
      _ = s := by rw [h1, h1]
  have hsc := hx.scalar s hs
  rw [h1, h2] at hsc
  have hsZ : s ∈ Z := by
    have e : s = (s * s * s) * (s * s)⁻¹ := by group
    rw [e]
    exact Z.mul_mem hsc (Z.inv_mem (hS.sq s hs))
  by_contra h
  exact hx.conj_ne hS hsZ h hxs

theorem eq_one_of_mem_zpowers (hS2 : IsPGroup 2 S) (hx3 : x ^ 3 = 1) {w : G} (hwS : w ∈ S)
    (hw : w ∈ zpowers x) : w = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hw3 : (x ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨m, hm⟩ := hS2 ⟨_, hwS⟩
  have hm' : (x ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hc : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one hw3)
    (orderOf_dvd_of_pow_eq_one hm'))

theorem perm3_conj_cases : ∀ τ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    τ * σ * τ⁻¹ = σ ∨ τ * σ * τ⁻¹ = σ⁻¹ := by
  decide

theorem mem_normalizer_zpowers {c : G} (h : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) :
    c ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  have h' : c⁻¹ * x * c = x ∨ c⁻¹ * x * c = x⁻¹ := by
    rcases h with h | h
    · left
      calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹) * c := by rw [h]
        _ = x := by group
    · right
      calc c⁻¹ * x * c = c⁻¹ * (c * x * c⁻¹)⁻¹ * c := by rw [h, inv_inv]
        _ = x⁻¹ := by group
  have key : ∀ d : G, (d * x * d⁻¹ = x ∨ d * x * d⁻¹ = x⁻¹) → ∀ n ∈ zpowers x,
      d * n * d⁻¹ ∈ zpowers x := by
    intro d hd n hn
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    rcases hd with hd | hd <;> rw [hd]
    · exact zpow_mem (mem_zpowers x) j
    · exact zpow_mem (inv_mem (mem_zpowers x)) j
  rw [mem_normalizer_iff]
  intro n
  refine ⟨key c h n, fun hn => ?_⟩
  have h1 := key c⁻¹ (by rwa [inv_inv]) _ hn
  have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
  rwa [e] at h1

theorem semidirect [Finite G] {T : Subgroup G} (C : Coord S Z H) (hS : Special S Z)
    (hx : XData S Z x)
    {θ : ↥(H ⊔ zpowers x ⊔ T) →* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)}
    (hker : θ.ker = S.subgroupOf (H ⊔ zpowers x ⊔ T)) (hS2 : IsPGroup 2 S) (hx3 : orderOf x = 3)
    (hxH : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S) (hSK : S ≤ H ⊔ T ⊔ zpowers x) :
    S ⊓ ((H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G)) = ⊥ ∧
      S ⊔ ((H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G)) =
        H ⊔ T ⊔ zpowers x := by
  have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp hx.normS s).mp hs
  have hKK : H ⊔ T ⊔ zpowers x = H ⊔ zpowers x ⊔ T := sup_right_comm H T (zpowers x)
  refine ⟨?_, le_antisymm (sup_le hSK inf_le_left) fun k hk => ?_⟩
  ·
    rw [eq_bot_iff]
    intro s hs'
    obtain ⟨hs, hs2⟩ := Subgroup.mem_inf.mp hs'
    obtain ⟨-, hsN⟩ := Subgroup.mem_inf.mp hs2
    rw [mem_bot]
    have hsx : s * x * s⁻¹ ∈ zpowers x := (mem_normalizer_iff.mp hsN x).mp (mem_zpowers x)
    have hw : s * x * s⁻¹ * x⁻¹ = 1 := by
      refine eq_one_of_mem_zpowers hS2 hx.cube ?_ (mul_mem hsx (inv_mem (mem_zpowers x)))
      have e : s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) := by group
      rw [e]
      exact S.mul_mem hs (hxS _ (S.inv_mem hs))
    have hsx' : s * x = x * s := by
      calc s * x = (s * x * s⁻¹ * x⁻¹) * x * s := by group
        _ = x * s := by rw [hw, one_mul]
    refine eq_one_of_conj_x hS hx hs ?_
    rw [← hsx']
    group
  ·
    have hk' : k ∈ H ⊔ zpowers x ⊔ T := hKK ▸ hk
    obtain ⟨hx2, hx3', hx1⟩ := θ_x C hker hS2 hx3 hxH
    obtain ⟨g, hg, hgS⟩ : ∃ g : G, (g = x ∨ g = x⁻¹) ∧ k * x * k⁻¹ * g⁻¹ ∈ S := by
      have hθ : ∀ g (hg : g ∈ H ⊔ zpowers x ⊔ T),
          θ (⟨k, hk'⟩ * ⟨x, x_mem_K⟩ * ⟨k, hk'⟩⁻¹ * (⟨g, hg⟩)⁻¹) = 1 →
          k * x * k⁻¹ * g⁻¹ ∈ S := fun g hg h => (mem_ker_iff hker).mp h
      rcases perm3_conj_cases (θ ⟨k, hk'⟩).1 (θ ⟨x, x_mem_K⟩).1 hx3' hx1 with h | h
      · refine ⟨x, Or.inl rfl, hθ x x_mem_K ?_⟩
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, Prod.fst_inv, h,
            mul_inv_cancel, Prod.fst_one]
        · rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, Prod.snd_inv, hx2,
            mul_one, inv_one, mul_one, mul_inv_cancel, Prod.snd_one]
      · refine ⟨x⁻¹, Or.inr rfl, hθ x⁻¹ (inv_mem x_mem_K) ?_⟩
        have e : (⟨x⁻¹, inv_mem x_mem_K⟩ : ↥(H ⊔ zpowers x ⊔ T)) = (⟨x, x_mem_K⟩)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, inv_inv]
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, h, inv_mul_cancel,
            Prod.fst_one]
        · rw [Prod.snd_mul, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, hx2, mul_one, mul_one,
            mul_inv_cancel, Prod.snd_one]
    have hgx : ∀ c : G, c * g = g * c → c * x = x * c := by
      intro c hc
      rcases hg with rfl | rfl
      · exact hc
      · calc c * x = x * (x⁻¹ * c) * x := by group
          _ = x * (c * x⁻¹) * x := by rw [hc]
          _ = x * c := by group
    have hgS' : ∀ a ∈ S, a * g * a⁻¹ * g⁻¹ ∈ S := by
      intro a ha
      have e : a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) := by group
      rw [e]
      refine S.mul_mem ha ?_
      rcases hg with rfl | rfl
      · exact hxS _ (S.inv_mem ha)
      · have := (mem_normalizer_iff.mp (inv_mem hx.normS) a⁻¹).mp (S.inv_mem ha)
        simpa using this
    let f : S → S := fun a => ⟨a * g * (a : G)⁻¹ * g⁻¹, hgS' a a.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (a : G) * g * (a : G)⁻¹ * g⁻¹ = b * g * (b : G)⁻¹ * g⁻¹ := congrArg Subtype.val hab
      have h2 : ((b : G)⁻¹ * a) * g = g * ((b : G)⁻¹ * a) := by
        calc ((b : G)⁻¹ * a) * g = (b : G)⁻¹ * ((a : G) * g * (a : G)⁻¹ * g⁻¹) * g * a := by group
          _ = (b : G)⁻¹ * (b * g * (b : G)⁻¹ * g⁻¹) * g * a := by rw [h1]
          _ = g * ((b : G)⁻¹ * a) := by group
      have h3 := eq_one_of_conj_x hS hx (S.mul_mem (S.inv_mem b.2) a.2) (by
        have := hgx _ h2
        calc x * ((b : G)⁻¹ * a) * x⁻¹ = ((b : G)⁻¹ * a) * x * x⁻¹ := by rw [this]
          _ = (b : G)⁻¹ * a := by group)
      exact Subtype.ext (by
        calc (a : G) = b * ((b : G)⁻¹ * a) := by group
          _ = b := by rw [h3, mul_one])
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hgS⟩
    have ha' : (a : G) * g * (a : G)⁻¹ * g⁻¹ = k * x * k⁻¹ * g⁻¹ := congrArg Subtype.val ha
    have hconj : ((a : G)⁻¹ * k) * x * ((a : G)⁻¹ * k)⁻¹ = g := by
      have e : k * x * k⁻¹ = (a : G) * g * (a : G)⁻¹ := by
        calc k * x * k⁻¹ = (k * x * k⁻¹ * g⁻¹) * g := by group
          _ = ((a : G) * g * (a : G)⁻¹ * g⁻¹) * g := by rw [ha']
          _ = (a : G) * g * (a : G)⁻¹ := by group
      calc ((a : G)⁻¹ * k) * x * ((a : G)⁻¹ * k)⁻¹ = (a : G)⁻¹ * (k * x * k⁻¹) * a := by group
        _ = g := by rw [e]; group
    have hN : (a : G)⁻¹ * k ∈
        (H ⊔ T ⊔ zpowers x) ⊓ normalizer ((zpowers x : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨(H ⊔ T ⊔ zpowers x).mul_mem ((H ⊔ T ⊔ zpowers x).inv_mem (hSK a.2))
        hk, mem_normalizer_zpowers (by rw [hconj]; exact hg)⟩
    have e : k = (a : G) * ((a : G)⁻¹ * k) := by group
    rw [e]
    exact mul_mem (mem_sup_left a.2) (mem_sup_right hN)

namespace QSetting

theorem relIndex_fixS [Finite G] (C : Coord S Z H) (hD : QSetting S Z H x t z)
    {E : Subgroup (alternatingGroup (Fin 5))} (hE : Nat.card E = 4) :
    (C.fixS hD.hS E ⊓ hD.Q).relIndex (C.fixS hD.hS E) = 2 := by
  obtain ⟨-, -, h16, h8⟩ :=
    C.fixS_elem hD.hS hD.hHS hD.hx hD.hxH hD.hxH' hD.ht hD.hzZ hD.hz1 hD.hz hE
  have heq : C.fixS hD.hS E ⊓ hD.Q = C.fixS hD.hS E ⊓ hD.hS.Wt t := by
    apply le_antisymm
    · exact fun a ha => ⟨ha.1, hD.hS.mem_Wt_of_mem_Qt _ _ hD.ht.notS ha.2 ha.1.1⟩
    · exact fun a ha => ⟨ha.1, hD.hS.Wt_le_Qt _ _ ha.2⟩
  rw [heq]
  have h := Subgroup.relIndex_mul_card (C.fixS hD.hS E ⊓ hD.hS.Wt t) (C.fixS hD.hS E)
  rw [inf_eq_left.mpr inf_le_left, h8, h16] at h
  omega

theorem Q_le (hD : QSetting S Z H x t z) {T : Subgroup G} (hST : S ≤ T) (htT : t ∈ T) :
    hD.Q ≤ T :=
  hD.hS.Qt_le _ _ (hD.hS.Wt_le.trans hST) htT

end QSetting

end Sec2

open Sec2

theorem sec2LocalQ_of (h21 : Step21) (h24 : Step24) (h25 : Step25) (h26 : Step26)
    (h212 : Step212) : Sec2LocalQ := by
  intro G _ _ A R g E F T₀ u y hd
  have hset := hd.setting
  have hS : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hset
  obtain ⟨C⟩ := nonempty_coord h26 hset
  obtain ⟨-, hSH, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hset
  obtain ⟨-, hPE, -, -, -, -, -, -, hSPE, hSE⟩ := h21 G A R g E F hset
  obtain ⟨-, hPST, ⟨x, hx3, hxF4, hxcl, hxH, hxH', θ, hθ, hker⟩, -, -, -⟩ :=
    (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  have hx : XData (sec2S A R E F) (sec2Z A E F) x :=
    ⟨hxF4.1, hxF4.2.1, by rw [← hx3, pow_orderOf_eq_one], hxcl, hxF4.2.2⟩
  have hT₀2 : IsPGroup 2 T₀ := hd.sylow.isPGroup
  have hT2 : IsPGroup 2 (sec2T E T₀) := hT₀2.to_le inf_le_left
  have hST : sec2S A R E F ≤ sec2T E T₀ := le_sup_right.trans hPST
  have hS2 : IsPGroup 2 (sec2S A R E F) := hT2.to_le hST
  have hKN : sec2H E F ⊔ sec2T E T₀ ⊔ zpowers x ≤ normalizer (sec2S A R E F : Set G) :=
    sup_le (sup_le hHS (inf_le_left.trans hd.sylow.le)) (zpowers_le.mpr hxF4.1)
  obtain ⟨hinf, hsup⟩ := semidirect C hS hx hker hS2 hx3 hxH'
    (hSH.trans (le_sup_left.trans le_sup_left))
  have hPH : sec2P E ≤ sec2H E F := le_sup_left
  have hP4 : (sec2S A R E F).relIndex (sec2P E) = 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex E (sec2S A R E F ⊓ sec2P E) (sec2P E) hSPE.1
      inf_le_right
    rw [hSPE.2.1, hPE.2.1, Subgroup.inf_relIndex_right] at h1
    omega
  have hP4' : (sec2P E ⊓ sec2S A R E F).relIndex (sec2P E) = 4 := by
    rw [Subgroup.inf_relIndex_left]
    exact hP4
  obtain ⟨t₀, ht₀, h0, h1, h2⟩ := exists_t₀ C hθ hker hS2 hT2 hx3 hxH'
    (le_sup_left.trans hPST) hPH hP4'
  obtain ⟨t, htT, htt, htx, htS, htN, hcompl, hTH, -, -⟩ := exists_t C hker hSH hST hS2 hT2 hx3
    (θ_x C hker hS2 hx3 hxH') hKN hinf hsup ht₀ h0 h1 h2
  have ht : TData (sec2S A R E F) (sec2H E F) x t := ⟨htN, htt, htx, htS, hcompl⟩
  obtain ⟨z, hzZ, hz1, hz⟩ := exists_z hS hx ht
  have hD : QSetting (sec2S A R E F) (sec2Z A E F) (sec2H E F) x t z :=
    ⟨hS, hSH, hHS, hx, hxH, hxH', ht, hzZ, hz1, hz⟩
  have hyH : y ∈ sec2H E F := hd.uy.2.2.2.1.1.1
  have hy3 : orderOf y = 3 := hd.uy.2.2.2.2
  have hQHT : sec2H E F ⊔ sec2T E T₀ ≤ normalizer (hD.Q : Set G) :=
    C.le_normalizer_Qt hS hHS ht hTH
  refine ⟨hD.Q, C.isQ8Cube_Qt hS hHS hx ht hzZ hz1 hz, hD.Q_le hST htT,
    hQHT (mem_sup_left hyH), fun Q' hQ' hQ'T hyQ' => hD.eq_Q C hTH hyH hy3 hQ' hQ'T hyQ',
    hD.Q_le (hSH.trans le_sup_left) (mem_sup_right htT), hQHT, ?_⟩
  have hN := Coord.eq_fixS C hS hPH (hPH.trans hHS) (inf_le_left.trans hSE.1)
    (h25 G A R g E F hset)
  rw [hN]
  exact hD.relIndex_fixS C (by rw [C.card_map_φ hPH, hP4])

end CFSG.ComponentClassification.AS81
