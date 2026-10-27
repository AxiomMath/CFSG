module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26BenderAux
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Reduce

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem exists_sq_mem_of_not_mem {G : Type*} [Group G] {R N : Subgroup G} (hR : IsPGroup 2 R)
    {y : G} (hy : y ∈ R) (hyN : y ∉ N) : ∃ y₁ ∈ R, y₁ ∉ N ∧ y₁ ^ 2 ∈ N := by
  classical
  obtain ⟨k, hk⟩ := hR ⟨y, hy⟩
  have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ j, y ^ (2 ^ j) ∈ N := ⟨k, by rw [hk']; exact one_mem _⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hj₀, h, pow_zero, pow_one] at this
    exact hyN this
  refine ⟨y ^ (2 ^ (j₀ - 1)), pow_mem hy _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, show j₀ - 1 + 1 = j₀ by omega]
  exact Nat.find_spec hex

variable {Y : Type} [Group Y] [Finite Y]

theorem alpha26_core {K : Subgroup Y} [K.Normal] (hK : fusionIsBenderGroup K) (P : Sylow 2 Y)
    (hKP : K ⊔ (P : Subgroup Y) = ⊤) {𝒯 : Set (Subgroup Y)}
    (hle : ∀ T ∈ 𝒯, T ≤ (P : Subgroup Y))
    (hcomm : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ⁅T₁, T₂⁆ = ⊥)
    (hcl : fusionStronglyClosed (memberSet 𝒯) P) {R : Subgroup Y} (hR : R ∈ 𝒯) (hbig : IsBig R)
    (hC : ∀ γ ∈ memberSet 𝒯, γ ∉ centralizer (K : Set Y))
    (hout : ∃ T₀ : Sylow 2 K, ∀ γ ∈ memberSet 𝒯, ∀ x : K, γ * x * γ⁻¹ = x →
      x ∈ normalizer ((T₀ : Subgroup K) : Set K))
    {a : Y} (haR : a ∈ R) (haK : a ∈ K) (ha2 : orderOf a = 2) :
    R = (P : Subgroup Y) ⊓ K ∧ (∀ R' ∈ 𝒯, IsBig R' → R' = R) ∧ IsSzOrU3 K ∧ SylowShape R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (P : Subgroup Y) ⊓ K with hTdef
  set C := centralizer (K : Set Y) with hCdef
  set Z := sylowCenter T with hZdef
  set Γ := memberSet 𝒯 with hΓdef
  have hd := BenderExt.extData_of_benderData K (BenderExt.benderData_of_isBenderGroup hK) P hKP
  have hTK : T ≤ K := inf_le_right
  have hTP : T ≤ P := inf_le_left
  have hZT : Z ≤ T := sylowCenter_le T
  have hCP : C ≤ P := hd.centralizer_le
  have hRP : R ≤ P := hle R hR
  have hR2 : IsPGroup 2 R := P.isPGroup'.to_le hRP
  have hRΓ : ∀ x ∈ R, x ≠ 1 → x ∈ Γ := fun x hx hx1 => mem_memberSet hR hx hx1
  have hΓP : ∀ x ∈ Γ, x ∈ (P : Subgroup Y) := by
    rintro x ⟨-, T₁, hT₁, hx⟩
    exact hle T₁ hT₁ hx
  have hCPr : ∀ {T₁ : Subgroup Y}, T₁ ∈ 𝒯 → ∀ {x t : Y}, x ∈ Γ → t ∈ T₁ → x * t ≠ t * x →
      x ∈ T₁ := by
    intro T₁ hT₁ x t hx ht hxt
    obtain ⟨-, T₂, hT₂, hxT₂⟩ := hx
    by_cases h : T₂ = T₁
    · rwa [← h]
    · exact absurd (commute_of_commutator_eq_bot (hcomm T₂ hT₂ T₁ hT₁ h) hxT₂ ht) hxt
  have hRC : ∀ x ∈ R, x ∈ C → x = 1 := fun x hx hxC => by
    by_contra hx1
    exact hC x (hRΓ x hx hx1) hxC
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := hRΓ a haR ha1
  have haT : a ∈ T := mem_inf.mpr ⟨hRP haR, haK⟩
  have haa : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have haZ : a ∈ Z := hd.omega_one a haT haa
  have hZΓ : ∀ z ∈ Z, z ≠ 1 → z ∈ Γ := by
    intro z hz hz1
    obtain ⟨n, -, -, hnz⟩ := hd.trans a haZ z hz ha1 hz1
    rw [← hnz]
    exact hcl a haΓ n (by rw [hnz]; exact hTP (hZT hz))
  have hZcomm : ∀ z ∈ Z, ∀ t ∈ T, t * z = z * t := fun z hz => (mem_sylowCenter.mp hz).2
  have hCcomm : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k := fun c hc k hk => mem_centralizer_iff.mp hc k hk
  obtain ⟨T₀, hT₀⟩ := hout
  have hOUT : ∀ γ ∈ Γ, γ ^ 2 ∈ C → γ ∈ T ⊔ C := fun γ hγ hγ2 =>
    mem_sup_centralizer_of_sq hK P hKP (hΓP γ hγ) hγ2 ⟨T₀, hT₀ γ hγ⟩
  have hsqC : ∀ {p c : Y}, p ∈ Z → c ∈ C → (p * c) ^ 2 ∈ C := by
    intro p c hp hc
    have hpc := hCcomm c hc p (hTK (hZT hp))
    have hp2 := hd.sq_center p hp
    have e : (p * c) ^ 2 = p ^ 2 * c ^ 2 := by
      rw [sq, sq, sq]
      calc p * c * (p * c) = p * (c * p) * c := by group
        _ = p * (p * c) * c := by rw [← hpc]
        _ = p * p * (c * c) := by group
    rw [e, hp2, one_mul]
    exact pow_mem hc 2
  have hnotZC : ∀ y ∈ R, y ^ 2 ≠ 1 → ∀ p ∈ Z, ∀ c ∈ C, y ≠ p * c := by
    intro y hy hy2 p hp c hc hyeq
    have := hsqC hp hc
    rw [← hyeq] at this
    exact hy2 (hRC _ (pow_mem hy 2) this)
  obtain ⟨r, hrR, hr4⟩ := exists_orderOf_eq_four hR2 hbig.2
  have hr1 : r ≠ 1 := fun h => by rw [h, orderOf_one] at hr4; omega
  have hrΓ : r ∈ Γ := hRΓ r hrR hr1
  have hrP : r ∈ (P : Subgroup Y) := hRP hrR
  have hr2ne : r ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hr4]; norm_num)
  have hr2Γ : r ^ 2 ∈ Γ := hRΓ _ (pow_mem hrR 2) hr2ne
  have hr4' : (r ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = orderOf r by rw [hr4]]
    exact pow_orderOf_eq_one r
  have hr2TC : r ^ 2 ∈ T ⊔ C := hOUT _ hr2Γ (by rw [hr4']; exact one_mem _)
  have hout' : T ≤ R → ∀ y ∈ R, y ^ 2 ∈ T ⊔ C → y ∈ T ⊔ C := by
    intro hTR y hy hy2
    obtain ⟨t, ht, ht2⟩ := exists_sq_mem_centralizer hK P (hRP hy) hy2
    have hγR : t⁻¹ * y ∈ R := R.mul_mem (R.inv_mem (hTR ht)) hy
    by_cases hγ1 : t⁻¹ * y = 1
    · have : y = t := by
        calc y = t * (t⁻¹ * y) := by group
          _ = t := by rw [hγ1, mul_one]
      rw [this]
      exact mem_sup_left ht
    have h1 := hOUT _ (hRΓ _ hγR hγ1) ht2
    have : y = t * (t⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left ht) h1
  have hRTC : T ≤ R → R ≤ T ⊔ C := by
    intro hTR y hy
    by_contra hyTC
    obtain ⟨y₁, hy₁R, hy₁TC, hy₁2⟩ := exists_sq_mem_of_not_mem hR2 hy hyTC
    exact hy₁TC (hout' hTR y₁ hy₁R hy₁2)
  rcases isSzOrU3_or_abelian hK with hSz | hab
  swap
  ·
    exfalso
    obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
    have hTZ : T ≤ Z := by
      intro x hx
      have h := hab T' (show (⟨x, hTK hx⟩ : K) ∈ (T' : Subgroup K) by
        rw [hT', mem_subgroupOf]; exact hx)
      rw [hT'] at h
      exact (BenderExt.Bridge.mem_sylowCenter_subgroupOf hTK _).mp h
    have hrTC : r ∉ T ⊔ C := by
      intro h
      obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup_of_normal_right.mp h
      exact hnotZC _ hrR hr2ne p (hTZ hp) c hc rfl
    obtain ⟨t₀, ht₀, ht₀r⟩ : ∃ t₀ ∈ T, t₀ * r ≠ r * t₀ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨-, -, t, ht, htZ⟩ := hd.aut r hrP (fun z hz => (hcon z (hZT hz)).symm) hrTC
      apply htZ
      have : r * t * r⁻¹ = t := by rw [← hcon t ht, mul_inv_cancel_right]
      rw [this, inv_mul_cancel]
      exact one_mem _
    have hTR : T ≤ R := by
      have hmem : ∀ t ∈ T, t * r ≠ r * t → t ∈ R := fun t ht htr =>
        hCPr hR (hZΓ t (hTZ ht) (fun h => htr (by rw [h, one_mul, mul_one]))) hrR htr
      intro t ht
      by_cases htr : t * r = r * t
      · have h1 : t₀ * t * r ≠ r * (t₀ * t) := by
          intro h
          apply ht₀r
          have : t₀ * r * t = r * t₀ * t := by
            calc t₀ * r * t = t₀ * (r * t) := by group
              _ = t₀ * (t * r) := by rw [htr]
              _ = r * (t₀ * t) := by rw [← mul_assoc, h]
              _ = r * t₀ * t := by group
          exact mul_right_cancel this
        have h2 := hmem _ (T.mul_mem ht₀ ht) h1
        have h3 := hmem _ ht₀ ht₀r
        have : t = t₀⁻¹ * (t₀ * t) := by group
        rw [this]
        exact R.mul_mem (R.inv_mem h3) h2
      · exact hmem t ht htr
    exact hrTC (hout' hTR r hrR hr2TC)
  have hZcomm' : ∀ {y : Y}, y ∈ (P : Subgroup Y) → y ^ 2 ∈ T ⊔ C → ∀ z ∈ Z, y * z = z * y :=
    fun hy hy2 => commute_center_of_sq hK hSz P hy hy2
  obtain ⟨s, hsR, hsT, hsZ⟩ : ∃ s ∈ R, s ∈ T ∧ s ∉ Z := by
    by_cases hrTC : r ∈ T ⊔ C
    · obtain ⟨p, hp, c, hc, hpc⟩ := mem_sup_of_normal_right.mp hrTC
      have hpZ : p ∉ Z := fun hpZ => hnotZC r hrR hr2ne p hpZ c hc hpc.symm
      obtain ⟨n, hnK, hnN, hpair⟩ := hd.cent p hp hpZ
      have hp'T : n⁻¹ * p * n ∈ T := (mem_normalizer_iff''.mp hnN p).mp hp
      have hcn : n⁻¹ * c * n = c := by
        have := hCcomm c hc n hnK
        calc n⁻¹ * c * n = n⁻¹ * (c * n) := by group
          _ = n⁻¹ * (n * c) := by rw [this]
          _ = c := by group
      have hconj : n⁻¹ * r * n = (n⁻¹ * p * n) * c := by
        rw [← hpc]
        calc n⁻¹ * (p * c) * n = (n⁻¹ * p * n) * (n⁻¹ * c * n) := by group
          _ = (n⁻¹ * p * n) * c := by rw [hcn]
      have hr'P : n⁻¹ * r * n ∈ (P : Subgroup Y) := by
        rw [hconj]
        exact P.mul_mem (hTP hp'T) (hCP hc)
      have hr'Γ : n⁻¹ * r * n ∈ Γ := hcl r hrΓ n hr'P
      have hcp : p * c = c * p := hCcomm c hc p (hTK hp)
      have hcp' : (n⁻¹ * p * n) * c = c * (n⁻¹ * p * n) := hCcomm c hc _ (hTK hp'T)
      have hnc : n⁻¹ * r * n * r ≠ r * (n⁻¹ * r * n) := by
        intro h
        rw [hconj, ← hpc] at h
        have h' : (n⁻¹ * p * n) * p * (c * c) = p * (n⁻¹ * p * n) * (c * c) := by
          calc (n⁻¹ * p * n) * p * (c * c) = ((n⁻¹ * p * n) * c) * (p * c) := by
                rw [mul_assoc (n⁻¹ * p * n) c, ← mul_assoc c p c, ← hcp]; group
            _ = (p * c) * ((n⁻¹ * p * n) * c) := h
            _ = p * (n⁻¹ * p * n) * (c * c) := by
                rw [mul_assoc p c, ← mul_assoc c (n⁻¹ * p * n) c, ← hcp']; group
        exact hpZ (hpair p hp rfl (mul_right_cancel h').symm)
      have hr'R : n⁻¹ * r * n ∈ R := hCPr hR hr'Γ hrR hnc
      refine ⟨(n⁻¹ * p * n) * p⁻¹, ?_, T.mul_mem hp'T (T.inv_mem hp), ?_⟩
      · have : (n⁻¹ * p * n) * p⁻¹ = (n⁻¹ * r * n) * r⁻¹ := by
          rw [hconj, ← hpc]
          group
        rw [this]
        exact R.mul_mem hr'R (R.inv_mem hrR)
      · intro hsZ
        apply hpZ
        refine hpair p hp rfl ?_
        have hc' := hZcomm _ hsZ p hp
        calc p * (n⁻¹ * p * n) = p * ((n⁻¹ * p * n) * p⁻¹) * p := by group
          _ = (n⁻¹ * p * n) * p⁻¹ * p * p := by rw [hc']
          _ = (n⁻¹ * p * n) * p := by group
    · have hrZ := hZcomm' hrP hr2TC
      obtain ⟨p, hp, c, hc, hpc⟩ := mem_sup_of_normal_right.mp hr2TC
      have hpK : p ∈ K := hTK hp
      have hp2 : p ^ 2 = 1 := by
        have hcp := hCcomm c hc p hpK
        have h1 : (p * c) ^ 2 = 1 := by rw [hpc]; exact hr4'
        have h2 : p ^ 2 * c ^ 2 = 1 := by
          rw [← h1, sq, sq, sq]
          calc p * p * (c * c) = p * (p * c) * c := by group
            _ = p * (c * p) * c := by rw [hcp]
            _ = p * c * (p * c) := by group
        have h3 : p ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h2
        have h4 : p ^ 2 ∈ K ⊓ C := mem_inf.mpr ⟨pow_mem hpK 2, h3 ▸ inv_mem (pow_mem hc 2)⟩
        rw [hd.inf_centralizer, mem_bot] at h4
        exact h4
      have hpZ : p ∈ Z := hd.omega_one p hp hp2
      have hfix := fix_le_center hK P hrP hrZ hrTC hpZ hc hpc.symm
      obtain ⟨-, -, x, hxT, hxZ⟩ := hd.aut r hrP hrZ hrTC
      have hxP : x ∈ (P : Subgroup Y) := hTP hxT
      have hmT : x⁻¹ * (r * x * r⁻¹) ∈ T := T.mul_mem (T.inv_mem hxT) (conj_mem_inf hrP hxT)
      have hr'P : x⁻¹ * r * x ∈ (P : Subgroup Y) :=
        P.mul_mem (P.mul_mem (P.inv_mem hxP) hrP) hxP
      have hr'Γ : x⁻¹ * r * x ∈ Γ := hcl r hrΓ x hr'P
      have hr'eq : x⁻¹ * r * x = x⁻¹ * (r * x * r⁻¹) * r := by group
      have hnc : x⁻¹ * r * x * r ≠ r * (x⁻¹ * r * x) := by
        intro h
        apply hxZ
        apply hfix _ hmT
        rw [hr'eq] at h
        have h' : x⁻¹ * (r * x * r⁻¹) * r = r * (x⁻¹ * (r * x * r⁻¹)) :=
          mul_right_cancel (h.trans (by group))
        calc r * (x⁻¹ * (r * x * r⁻¹)) * r⁻¹ = x⁻¹ * (r * x * r⁻¹) * r * r⁻¹ := by rw [← h']
          _ = x⁻¹ * (r * x * r⁻¹) := by group
      have hr'R : x⁻¹ * r * x ∈ R := hCPr hR hr'Γ hrR hnc
      refine ⟨x⁻¹ * (r * x * r⁻¹), ?_, hmT, hxZ⟩
      have : x⁻¹ * (r * x * r⁻¹) = (x⁻¹ * r * x) * r⁻¹ := by group
      rw [this]
      exact R.mul_mem hr'R (R.inv_mem hrR)
  have hs1 : s ≠ 1 := fun h => hsZ (by rw [h]; exact one_mem _)
  have hsΓ : s ∈ Γ := hRΓ s hsR hs1
  obtain ⟨n, hnK, hnN, hpair⟩ := hd.cent s hsT hsZ
  have hs'T : n⁻¹ * s * n ∈ T := (mem_normalizer_iff''.mp hnN s).mp hsT
  have hs'Γ : n⁻¹ * s * n ∈ Γ := hcl s hsΓ n (hTP hs'T)
  have hss' : n⁻¹ * s * n * s ≠ s * (n⁻¹ * s * n) := fun h => hsZ (hpair s hsT rfl h.symm)
  have hs'R : n⁻¹ * s * n ∈ R := hCPr hR hs'Γ hsR hss'
  have hΓT : ∀ x ∈ Γ, x ∈ T → x ∈ R ∨ x ∈ Z := by
    intro x hx hxT
    by_cases h1 : x * s = s * x
    · by_cases h2 : x * (n⁻¹ * s * n) = n⁻¹ * s * n * x
      · exact Or.inr (hpair x hxT h1 h2)
      · exact Or.inl (hCPr hR hx hs'R h2)
    · exact Or.inl (hCPr hR hx hsR h1)
  have hZR : Z ≤ R := by
    have hc : ⁅R ⊓ T, Z⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro z hz
      exact (hZcomm z hz x (mem_inf.mp hx).2).symm
    rcases hd.nest (R ⊓ T) Z inf_le_right hZT hc (fun b hb k hk hbk => by
      by_cases hb1 : b = 1
      · left
        rw [hb1, mul_one, inv_mul_cancel]
        exact one_mem _
      have hbΓ : b ∈ Γ := by
        rcases hb with hb | hb
        · exact hRΓ b (mem_inf.mp hb).1 hb1
        · exact hZΓ b hb hb1
      rcases hΓT _ (hcl b hbΓ k (hTP hbk)) hbk with h | h
      · exact Or.inl (mem_inf.mpr ⟨h, hbk⟩)
      · exact Or.inr h) with h | h
    · exact absurd (h (mem_inf.mpr ⟨hsR, hsT⟩)) hsZ
    · exact h.trans inf_le_left
  have hTR : T ≤ R := by
    have heq := eq_of_irr hSz P (A := R ⊓ T) (le_inf hZR hZT) inf_le_right
      (fun m hm hmN x hx => by
        by_cases hx1 : x = 1
        · rw [hx1, mul_one, inv_mul_cancel]
          exact one_mem _
        have hxT : m⁻¹ * x * m ∈ T := (mem_normalizer_iff''.mp hmN x).mp (mem_inf.mp hx).2
        have hxΓ := hcl x (hRΓ x (mem_inf.mp hx).1 hx1) m (hTP hxT)
        rcases hΓT _ hxΓ hxT with h | h
        · exact mem_inf.mpr ⟨h, hxT⟩
        · exact mem_inf.mpr ⟨hZR h, hxT⟩)
      (fun hle' => hsZ (hle' (mem_inf.mpr ⟨hsR, hsT⟩)))
    have heq' : R ⊓ T = T := heq
    calc T = R ⊓ T := heq'.symm
      _ ≤ R := inf_le_left
  have hRT : R = T := by
    refine le_antisymm (fun y hy => ?_) hTR
    obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup_of_normal_right.mp (hRTC hTR hy)
    have hcR : c ∈ R := by
      have : c = p⁻¹ * (p * c) := by group
      rw [this]
      exact R.mul_mem (R.inv_mem (hTR hp)) hy
    rw [hRC c hcR hc, mul_one]
    exact hp
  refine ⟨hRT, ?_, hSz, ?_⟩
  ·
    intro R' hR' hbig'
    by_contra hne
    have hRR' := hcomm R' hR' R hR hne
    obtain ⟨y, hyR', hy4⟩ := exists_orderOf_eq_four (P.isPGroup'.to_le (hle R' hR')) hbig'.2
    have hyP : y ∈ (P : Subgroup Y) := hle R' hR' hyR'
    have hyT : ∀ t ∈ T, y * t = t * y := fun t ht =>
      commute_of_commutator_eq_bot hRR' hyR' (hTR ht)
    have hyTC : y ∈ T ⊔ C := by
      by_contra h
      obtain ⟨-, -, t, ht, htZ⟩ := hd.aut y hyP (fun z hz => hyT z (hZT hz)) h
      apply htZ
      rw [hyT t ht, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
    obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hyTC
    have hpZ : p ∈ Z := by
      refine mem_sylowCenter.mpr ⟨hp, fun t ht => ?_⟩
      have h1 := hyT t ht
      have h2 := hCcomm c hc t (hTK ht)
      have : (p * c) * t * c⁻¹ = t * (p * c) * c⁻¹ := by rw [h1]
      calc t * p = t * (p * c) * c⁻¹ := by group
        _ = (p * c) * t * c⁻¹ := this.symm
        _ = p * (c * t) * c⁻¹ := by group
        _ = p * (t * c) * c⁻¹ := by rw [h2]
        _ = p * t := by group
    have hy2 : (p * c) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hy4]; norm_num)
    exact hC _ (mem_memberSet hR' (pow_mem hyR' 2) hy2) (hsqC hpZ hc)
  ·
    have hRZ : ∀ x ∈ R, (∀ y ∈ R, y * x = x * y) ↔ x ∈ Z := fun x hx => by
      rw [hRT] at hx ⊢
      exact ⟨fun h => mem_sylowCenter.mpr ⟨hx, h⟩, fun h => (mem_sylowCenter.mp h).2⟩
    have hcen : ∀ x : R, x ∈ center R ↔ (x : Y) ∈ Z := fun x => by
      rw [← hRZ x x.2, mem_center_iff]
      constructor
      · intro h y hy
        exact congrArg Subtype.val (h ⟨y, hy⟩)
      · intro h y
        exact Subtype.ext (h y y.2)
    refine ⟨fun x hx => ?_, fun z hz => ?_, ?_, fun hcomm' => ?_⟩
    · rw [hcen]
      have hxT : (x : Y) ∈ T := hRT ▸ x.2
      exact hd.omega_one _ hxT (by simpa using congrArg Subtype.val hx)
    · exact Subtype.ext (by simpa using hd.sq_center _ ((hcen z).mp hz))
    · have hmap : (center R).map R.subtype = Z := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (hcen x).mp hx
        · intro hy
          have hyR : y ∈ R := hRT ▸ hZT hy
          exact ⟨⟨y, hyR⟩, (hcen _).mpr hy, rfl⟩
      rw [← card_map_of_injective R.subtype_injective, hmap]
      exact hd.card_center
    · apply hbig.2
      refine ⟨hcomm', fun x hx => ?_⟩
      have hxZ : x ∈ Z := (hRZ x hx).mp fun y hy =>
        congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : R) ⟨x, hx⟩)
      exact hd.sq_center x hxZ

end CFSG.ComponentClassification.Asc76.L26
