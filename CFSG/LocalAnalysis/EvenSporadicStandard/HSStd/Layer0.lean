module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PerfectLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSmallLie

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem orderOf_pow_two_pow_pred {s : G} {n : ℕ} (hn : 1 ≤ n) (hs : orderOf s = 2 ^ n) :
    orderOf (s ^ 2 ^ (n - 1)) = 2 := by
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hs]; exact pow_dvd_pow 2 (Nat.sub_le n 1)), hs,
    Nat.pow_div (Nat.sub_le n 1) (by norm_num)]
  have : n - (n - 1) = 1 := by omega
  rw [this]

omit [Finite G] in
theorem eq_one_of_mem_of_mem_centralizer (hZ : center L = ⊥) {c : G} (hL : c ∈ L)
    (hC : c ∈ centralizer (L : Set G)) : c = 1 := by
  have h1 : c ∈ L ⊓ centralizer (L : Set G) := ⟨hL, hC⟩
  rw [← map_center_eq_inf_centralizer, hZ, Subgroup.map_bot] at h1
  exact h1

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.false_of_full_conj_config
    (h : StdHyp G L) (hZ : center L = ⊥)
    (hd : LayerZeroData L) (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (hS4 : 4 ≤ Nat.card S) {g' : G} (hg' : g' ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hTg : T ≤ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom)
    (hTN : T ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T) (hTcard : Nat.card T = Nat.card S) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hodd, hNC, -⟩ := h.standard
  have hgC : g' ∉ normalizer ((centralizer (L : Set G)) : Set G) := by rwa [hNC]
  have hTC : ∀ y ∈ T, y ∈ (centralizer (L : Set G)) → y = 1 := by
    intro y hyT hyC
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hyT⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hyC, hTg hyT⟩ :
      y ∈ (centralizer (L : Set G)) ⊓ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr (hodd g' hgC))
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hTcyc : IsCyclic T := (isCyclic_and_card_le_of_le_conj S hS hTg hT).1
  obtain ⟨⟨s, hsT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hsord : orderOf s = Nat.card S := by
    have h' := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk, hTcard] at h'
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h4 : 4 ≤ 2 ^ n := hn ▸ hS4
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsn : orderOf s = 2 ^ n := by rw [hsord, hn]
  have hsC' : s ∈ (normalizer (L : Set G)) := hTN hsT
  set t₁ : G := s ^ 2 ^ (n - 1) with ht₁def
  have ht₁T : t₁ ∈ T := Subgroup.pow_mem _ hsT _
  have ht₁2 : orderOf t₁ = 2 := orderOf_pow_two_pow_pred (by omega) hsn
  have ht₁1 : t₁ * t₁ = 1 := by rw [← sq, ← ht₁2, pow_orderOf_eq_one]
  obtain ⟨c_t, hc_tC, hct⟩ := Subgroup.mem_map.mp (hTg ht₁T)
  have hct' : g' * c_t * g'⁻¹ = t₁ := by simpa [MulAut.conj_apply] using hct
  have hct2 : orderOf c_t = 2 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj g') c_t]
    simp only [MulAut.conj_apply]
    rw [hct', ht₁2]
  obtain ⟨S', hS'cyc, hcS'⟩ := h.exists_cyclic_sylow_mem hc_tC hct2
  have hE : (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) =
      (S' : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    h.centralizer_inf_centralizer_eq_map_sylow hc_tC hct2 S' hS'cyc hcS'
  have hS'card : Nat.card ((S' : Subgroup (centralizer (L : Set G))).map
      (centralizer (L : Set G)).subtype) = Nat.card S := by
    rw [Subgroup.card_map_of_injective (centralizer (L : Set G)).subtype_injective]
    exact Nat.card_congr (Sylow.equiv S' S).toEquiv
  set T₀ : Subgroup G := T.map (MulAut.conj g'⁻¹).toMonoidHom with hT₀def
  have hT₀le : T₀ ≤ (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hwC, hw⟩ := Subgroup.mem_map.mp (hTg hy)
    have hw' : g' * w * g'⁻¹ = y := by simpa using hw
    have hyw : (MulAut.conj g'⁻¹).toMonoidHom y = w := by
      show g'⁻¹ * y * g'⁻¹⁻¹ = w
      rw [inv_inv, ← hw']; group
    rw [hyw]
    refine Subgroup.mem_inf.mpr ⟨hwC, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm : t₁ * y = y * t₁ := mul_comm_of_mem_isCyclic hTcyc ht₁T hy
    have hcteq : c_t = g'⁻¹ * t₁ * g' := by rw [← hct']; group
    have hwy : w = g'⁻¹ * y * g' := by rw [← hw']; group
    rw [hcteq, hwy]
    calc g'⁻¹ * y * g' * (g'⁻¹ * t₁ * g') = g'⁻¹ * (y * t₁) * g' := by group
      _ = g'⁻¹ * (t₁ * y) * g' := by rw [hcomm]
      _ = g'⁻¹ * t₁ * g' * (g'⁻¹ * y * g') := by group
  have hT₀card : Nat.card T₀ = Nat.card S := by
    rw [hT₀def, Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective, hTcard]
  have hT₀eq : T₀ = (centralizer (L : Set G)) ⊓ centralizer ({c_t} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hT₀le (by rw [hE, hS'card, hT₀card])
  have hnormT : ∀ x : G, x * t₁ = t₁ * x → ∀ y ∈ T, x * y * x⁻¹ ∈ T := by
    intro x hx y hy
    set x₀ : G := g'⁻¹ * x * g' with hx₀
    have hx₀c : x₀ * c_t = c_t * x₀ := by
      have e1 : x * (g' * c_t * g'⁻¹) = (g' * c_t * g'⁻¹) * x := by rw [hct']; exact hx
      calc x₀ * c_t = g'⁻¹ * (x * (g' * c_t * g'⁻¹)) * g' := by rw [hx₀]; group
        _ = g'⁻¹ * ((g' * c_t * g'⁻¹) * x) * g' := by rw [e1]
        _ = c_t * x₀ := by rw [hx₀]; group
    have hx₀N : x₀ ∈ (normalizer (L : Set G)) := h.centralizer_le_normalizer hc_tC hct2
      (mem_centralizer_singleton_iff.mpr hx₀c)
    have hx₀NC : x₀ ∈ normalizer ((centralizer (L : Set G)) : Set G) := by rw [hNC]; exact hx₀N
    have hy₀ : g'⁻¹ * y * g' ∈ T₀ := ⟨y, hy, by simp⟩
    rw [hT₀eq] at hy₀
    obtain ⟨hy₀C, hy₀c⟩ := hy₀
    have hy₀c' : g'⁻¹ * y * g' * c_t = c_t * (g'⁻¹ * y * g') :=
      mem_centralizer_singleton_iff.mp hy₀c
    have hxinv : x₀⁻¹ * c_t = c_t * x₀⁻¹ := by
      calc x₀⁻¹ * c_t = x₀⁻¹ * (c_t * x₀) * x₀⁻¹ := by group
        _ = x₀⁻¹ * (x₀ * c_t) * x₀⁻¹ := by rw [hx₀c]
        _ = c_t * x₀⁻¹ := by group
    have hmC : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ (centralizer (L : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp hx₀NC _).mp hy₀C
    have hmc : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ centralizer ({c_t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x₀ * (g'⁻¹ * y * g') * x₀⁻¹ * c_t
          = x₀ * (g'⁻¹ * y * g') * (x₀⁻¹ * c_t) := by group
        _ = x₀ * (g'⁻¹ * y * g') * (c_t * x₀⁻¹) := by rw [hxinv]
        _ = x₀ * ((g'⁻¹ * y * g') * c_t) * x₀⁻¹ := by group
        _ = x₀ * (c_t * (g'⁻¹ * y * g')) * x₀⁻¹ := by rw [hy₀c']
        _ = (x₀ * c_t) * (g'⁻¹ * y * g') * x₀⁻¹ := by group
        _ = (c_t * x₀) * (g'⁻¹ * y * g') * x₀⁻¹ := by rw [hx₀c]
        _ = c_t * (x₀ * (g'⁻¹ * y * g') * x₀⁻¹) := by group
    have hmem : x₀ * (g'⁻¹ * y * g') * x₀⁻¹ ∈ T₀ := by
      rw [hT₀eq]; exact Subgroup.mem_inf.mpr ⟨hmC, hmc⟩
    obtain ⟨τ, hτ, hτe⟩ := Subgroup.mem_map.mp hmem
    have hτe' : g'⁻¹ * τ * g' = x₀ * (g'⁻¹ * y * g') * x₀⁻¹ := by
      simpa [MulAut.conj_apply] using hτe
    have : x * y * x⁻¹ = τ := by
      have h2 : τ = g' * (x₀ * (g'⁻¹ * y * g') * x₀⁻¹) * g'⁻¹ := by rw [← hτe']; group
      rw [h2, hx₀]; group
    rw [this]; exact hτ
  have hout := hd.2.1
  have hs2 : s ^ 2 ∈ L ⊔ (centralizer (L : Set G)) := h.sq_mem_sup_centralizer hout hsC'
  obtain ⟨l₂, hl₂, c₂, hc₂, hsq⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (A := L) (B := (centralizer (L : Set G))) le_rfl hs2
  have hlc : Commute l₂ c₂ := mem_centralizer_iff.mp hc₂ l₂ hl₂
  set z : G := l₂ ^ 2 ^ (n - 2) with hzdef
  set c : G := c₂ ^ 2 ^ (n - 2) with hcdef
  have hzL : z ∈ L := Subgroup.pow_mem _ hl₂ _
  have hcC : c ∈ (centralizer (L : Set G)) := Subgroup.pow_mem _ hc₂ _
  have hzc : Commute z c := hlc.pow_pow _ _
  have ht₁zc : t₁ = z * c := by
    have h2n : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [← pow_succ' 2 (n - 2)]; congr 1; omega
    rw [ht₁def, h2n, pow_mul, hsq, hlc.mul_pow]
  have hsq' : (z * c) * (z * c) = z * z * (c * c) := by
    calc (z * c) * (z * c) = z * (c * z) * c := by group
      _ = z * (z * c) * c := by rw [← hzc.eq]
      _ = z * z * (c * c) := by group
  have h1 : z * z * (c * c) = 1 := by rw [← hsq', ← ht₁zc, ht₁1]
  have hzz : z * z = 1 := by
    have hcc : c * c ∈ (centralizer (L : Set G)) := (centralizer (L : Set G)).mul_mem hcC hcC
    have hzzL : z * z ∈ L := L.mul_mem hzL hzL
    have hzzC : z * z ∈ (centralizer (L : Set G)) := by
      have : z * z = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact (centralizer (L : Set G)).inv_mem hcc
    exact eq_one_of_mem_of_mem_centralizer hZ hzzL hzzC
  have hcc1 : c * c = 1 := by rwa [hzz, one_mul] at h1
  have hz1 : z ≠ 1 := by
    intro hz1
    have : t₁ = c := by rw [ht₁zc, hz1, one_mul]
    have hc1' : t₁ = 1 := hTC t₁ ht₁T (this ▸ hcC)
    rw [hc1', orderOf_one] at ht₁2
    omega
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rwa [sq]) hz1
  set zL : L := ⟨z, hzL⟩ with hzLdef
  have hzL2 : orderOf zL = 2 := by rw [hzLdef, Subgroup.orderOf_mk]; exact hz2
  obtain ⟨hU1, hU2⟩ := hd.2.2 zL hzL2
  set a : MulAut L := L.normalizerMonoidHom ⟨s, hsC'⟩ with hadef
  have ha : ∀ x : L, ((a x : L) : G) = s * x * s⁻¹ := fun x => rfl
  have hasq : a * a ≠ 1 := by
    intro h1
    have hs2C : s ^ 2 ∈ (centralizer (L : Set G)) := by
      rw [mem_centralizer_iff]
      intro l hl
      have h3 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) h1
      have h3' : s * (s * l * s⁻¹) * s⁻¹ = l := h3
      calc l * s ^ 2 = (s * (s * l * s⁻¹) * s⁻¹) * (s * s) := by rw [h3', sq]
        _ = s ^ 2 * l := by rw [sq]; group
    have hs2T : s ^ 2 ∈ T := Subgroup.pow_mem _ hsT 2
    have := hTC _ hs2T hs2C
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one this
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  by_cases hc1 : c = 1
  ·
    have ht₁z : t₁ = z := by rw [ht₁zc, hc1, mul_one]
    rcases hU2 with ⟨P, hPle, hPP, hzP⟩ | hU2'
    ·
      set PG : Subgroup G := P.map L.subtype with hPG
      have hPGc : ⁅PG, PG⁆ = PG := by rw [hPG, ← Subgroup.map_commutator, hPP]
      set P₀ : Subgroup G := PG.map (MulAut.conj g'⁻¹).toMonoidHom with hP₀
      have hP₀c : ⁅P₀, P₀⁆ = P₀ := by rw [hP₀, ← Subgroup.map_commutator, hPGc]
      have hct_eq : c_t = g'⁻¹ * z * g' := by rw [← ht₁z, ← hct']; group
      have hP₀le : P₀ ≤ centralizer ({c_t} : Set G) := by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
        have hpz := mem_centralizer_singleton_iff.mp (hPle hp)
        have hpz' : (p : G) * z = z * (p : G) := congrArg Subtype.val hpz
        have e : (MulAut.conj g'⁻¹).toMonoidHom (L.subtype p) = g'⁻¹ * (p : G) * g' := by
          simp
        rw [e, mem_centralizer_singleton_iff, hct_eq]
        calc g'⁻¹ * (p : G) * g' * (g'⁻¹ * z * g') = g'⁻¹ * (p * z) * g' := by group
          _ = g'⁻¹ * (z * p) * g' := by rw [hpz']
          _ = g'⁻¹ * z * g' * (g'⁻¹ * (p : G) * g') := by group
      have hcP₀ : c_t ∈ P₀ := by
        refine ⟨z, ⟨zL, hzP, rfl⟩, ?_⟩
        simp [hct_eq]
      have hP₀L : P₀ ≤ L := h.le_of_perfect_of_le_centralizer hout hc_tC hct2 hP₀c hP₀le
      have := eq_one_of_mem_of_mem_centralizer hZ (hP₀L hcP₀) hc_tC
      rw [this, orderOf_one] at hct2
      omega
    ·
      apply hasq
      apply hU2' a
      intro x hx hxodd
      have hxz : (x : G) * z = z * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
      have hxt : (x : G) * t₁ = t₁ * (x : G) := by rw [ht₁z]; exact hxz
      have hxt' : (x : G)⁻¹ * t₁ = t₁ * (x : G)⁻¹ := by
        calc (x : G)⁻¹ * t₁ = (x : G)⁻¹ * (t₁ * x) * (x : G)⁻¹ := by group
          _ = (x : G)⁻¹ * (x * t₁) * (x : G)⁻¹ := by rw [hxt]
          _ = t₁ * (x : G)⁻¹ := by group
      have hxnorm : (x : G) ∈ normalizer (T : Set G) := by
        refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hnormT _ hxt y hy, fun hy => ?_⟩
        have := hnormT _ hxt' _ hy
        simpa [mul_assoc] using this
      have hxodd' : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
      have hcomm := commute_of_odd_of_mem_normalizer hT hxodd' hxnorm s hsT
      apply Subtype.ext
      rw [ha]
      calc s * (x : G) * s⁻¹ = (x : G) * s * s⁻¹ := by rw [← hcomm]
        _ = (x : G) := by group
  ·
    apply hasq
    apply hU1 a
    intro x hx
    have hxz : (x : G) * z = z * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    have hxc : (x : G) * c = c * (x : G) := mem_centralizer_iff.mp hcC x x.2
    have hxt : (x : G) * t₁ = t₁ * (x : G) := by
      rw [ht₁zc]
      calc (x : G) * (z * c) = (x * z) * c := by group
        _ = (z * x) * c := by rw [hxz]
        _ = z * (x * c) := by group
        _ = z * (c * x) := by rw [hxc]
        _ = z * c * x := by group
    have hxsT : (x : G) * s * (x : G)⁻¹ ∈ T := hnormT _ hxt s hsT
    have huT : (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ T := T.mul_mem hxsT (T.inv_mem hsT)
    have huL : (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ L := by
      have h1 : s * (x : G)⁻¹ * s⁻¹ ∈ L := by
        have := (a x⁻¹).2
        rwa [ha, Subgroup.coe_inv] at this
      have := L.mul_mem x.2 h1
      simpa [mul_assoc] using this
    have hu1 : (x : G) * s * (x : G)⁻¹ * s⁻¹ = 1 := by
      by_contra hne
      obtain ⟨k, hk⟩ := exists_pow_eq_of_ne_one hT ht₁T ht₁2 huT hne
      have ht₁L : t₁ ∈ L := by rw [← hk]; exact Subgroup.pow_mem _ huL k
      have hcL : c ∈ L := by
        have : c = z⁻¹ * t₁ := by rw [ht₁zc]; group
        rw [this]; exact L.mul_mem (L.inv_mem hzL) ht₁L
      exact hc1 (eq_one_of_mem_of_mem_centralizer hZ hcL hcC)
    apply Subtype.ext
    rw [ha]
    have h2 : (x : G) * s = s * x := by
      calc (x : G) * s = (x * s * (x : G)⁻¹ * s⁻¹) * (s * x) := by group
        _ = s * x := by rw [hu1, one_mul]
    calc s * (x : G) * s⁻¹ = (x : G) * s * s⁻¹ := by rw [← h2]
      _ = (x : G) := by group

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_of_layerZeroData
    (h : StdHyp G L) (hZ : center L = ⊥) (hd : LayerZeroData L)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := h.toStandardSetting
  have hS := hset.isCyclic_sylow S
  have h2 : 2 ∣ Nat.card S := S.dvd_card_of_dvd_card (even_iff_two_dvd.mp hset.standard.2.1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  by_contra hne
  have hS4 : 4 ≤ Nat.card S := by
    rw [hn] at h2 hne ⊢
    rcases n with _ | _ | n
    · norm_num at h2
    · norm_num at hne
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact hset.false_of_forall_card_le_two hd.1 S hS4 hall
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
      rw [hm] at hPcard ⊢
      rcases m with _ | _ | m
      · norm_num at hPcard
      · norm_num at hPcard
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hset.standard S hS hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hP2 hP4
    exact h.false_of_full_conj_config hZ hd S hS hS4 hg' hTg hTN hT hTcard

end CFSG.EvenSporadicStandard.HSStd
