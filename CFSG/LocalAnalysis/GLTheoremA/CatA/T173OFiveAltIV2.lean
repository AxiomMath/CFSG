module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XFamily
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

private lemma map_centralizer_conj_of_centralizes {G : Type*} [Group G] {g : G} {s : Set G}
    (h : ∀ y ∈ s, g * y * g⁻¹ = y) :
    (Subgroup.centralizer s).map (MulAut.conj g).toMonoidHom = Subgroup.centralizer s := by
  have hgy : ∀ y ∈ s, g⁻¹ * y * g = y := by
    intro y hy
    have h1 : g * y = y * g := by
      calc g * y = (g * y * g⁻¹) * g := by group
        _ = y * g := by rw [h y hy]
    calc g⁻¹ * y * g = g⁻¹ * (y * g) := by group
      _ = g⁻¹ * (g * y) := by rw [h1]
      _ = y := by group
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    calc y * (g * c * g⁻¹) = g * (g⁻¹ * y * g) * c * g⁻¹ := by group
      _ = g * y * c * g⁻¹ := by rw [hgy y hy]
      _ = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [hc y hy]
      _ = (g * c * g⁻¹) * y := by
        have hy' : g⁻¹ * y = y * g⁻¹ := by
          calc g⁻¹ * y = (g⁻¹ * y * g) * g⁻¹ := by group
            _ = y * g⁻¹ := by rw [hgy y hy]
        calc g * (c * y) * g⁻¹ = g * c * (y * g⁻¹) := by group
          _ = g * c * (g⁻¹ * y) := by rw [← hy']
          _ = (g * c * g⁻¹) * y := by group
  · intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hmem : g⁻¹ * x * g ∈ Subgroup.centralizer s := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * (g⁻¹ * x * g) = g⁻¹ * (g * y * g⁻¹) * x * g := by group
        _ = g⁻¹ * y * x * g := by rw [h y hy]
        _ = g⁻¹ * (y * x) * g := by group
        _ = g⁻¹ * (x * y) * g := by rw [hx y hy]
        _ = g⁻¹ * x * y * g := by group
        _ = g⁻¹ * x * (g * y * g⁻¹) * g := by rw [h y hy]
        _ = (g⁻¹ * x * g) * y := by group
    refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g, hmem, ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

private lemma B_le_normalizer_K [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) : B ≤ Subgroup.normalizer (K : Set Ω) := by
  have hKeq : K = GLALayer (S ⊓ Subgroup.centralizer (D : Set Ω)) := hcfg.std.2.2.2.2.1
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcommD : ∀ d ∈ D, b * d * b⁻¹ = d := by
    intro d hd
    rw [isElemAbelian_commute hcfg.elem hb (hcfg.std.1 hd), mul_assoc, mul_inv_cancel, mul_one]
  have hSmap : S.map (MulAut.conj b).toMonoidHom = S := by
    haveI : S.Normal := hcfg.normal
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1
      (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top b)
  have hCmap : (Subgroup.centralizer (D : Set Ω)).map (MulAut.conj b).toMonoidHom =
      Subgroup.centralizer (D : Set Ω) :=
    map_centralizer_conj_of_centralizes hcommD
  have harg : (S ⊓ Subgroup.centralizer (D : Set Ω)).map (MulAut.conj b).toMonoidHom =
      S ⊓ Subgroup.centralizer (D : Set Ω) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective, hSmap, hCmap]
  calc K.map (MulAut.conj b).toMonoidHom
      = (GLALayer (S ⊓ Subgroup.centralizer (D : Set Ω))).map
          (MulAut.conj b).toMonoidHom := by rw [hKeq]
    _ = GLALayer ((S ⊓ Subgroup.centralizer (D : Set Ω)).map
          (MulAut.conj b).toMonoidHom) :=
        (Y10F.glaLayer_map (MulAut.conj b).injective _).symm
    _ = GLALayer (S ⊓ Subgroup.centralizer (D : Set Ω)) := by rw [harg]
    _ = K := hKeq.symm

private def mapToPiImg (M : S172DModel S B G₀ Ghat) (X : Subgroup Ω) (hXS : X ≤ S) :
    ↥X →* ↥(M.piImg X) where
  toFun y :=
    ⟨((M.π ⟨(y : Ω), hXS y.2⟩ : ↥G₀) : Γ),
      Subgroup.mem_map_of_mem G₀.subtype
        (Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 y.2))⟩
  map_one' := by
    apply Subtype.ext
    show ((M.π ⟨1, hXS X.one_mem⟩ : ↥G₀) : Γ) = ((1 : ↥G₀) : Γ)
    rw [show (⟨1, hXS X.one_mem⟩ : ↥S) = 1 from rfl, map_one]
  map_mul' a b := by
    apply Subtype.ext
    show ((M.π ⟨(a : Ω) * (b : Ω), hXS (X.mul_mem a.2 b.2)⟩ : ↥G₀) : Γ) =
      ((M.π ⟨(a : Ω), hXS a.2⟩ : ↥G₀) : Γ) *
        ((M.π ⟨(b : Ω), hXS b.2⟩ : ↥G₀) : Γ)
    rw [show (⟨(a : Ω) * (b : Ω), hXS (X.mul_mem a.2 b.2)⟩ : ↥S) =
      (⟨(a : Ω), hXS a.2⟩ : ↥S) * ⟨(b : Ω), hXS b.2⟩ from rfl, map_mul]
    rfl

private lemma mapToPiImg_surjective (M : S172DModel S B G₀ Ghat) (X : Subgroup Ω)
    (hXS : X ≤ S) : Function.Surjective (mapToPiImg M X hXS) := by
  intro z
  obtain ⟨g, hg, hgΓ⟩ := Subgroup.mem_map.1 z.2
  obtain ⟨s, hs, hsπ⟩ := Subgroup.mem_map.1 hg
  have hsX : (s : Ω) ∈ X := (Subgroup.mem_subgroupOf (H := X) (K := S)).1 hs
  refine ⟨⟨(s : Ω), hsX⟩, ?_⟩
  apply Subtype.ext
  calc ((M.π ⟨(s : Ω), hXS hsX⟩ : ↥G₀) : Γ) = ((M.π s : ↥G₀) : Γ) := rfl
    _ = (g : Γ) := congrArg G₀.subtype hsπ
    _ = (z : Γ) := hgΓ

private lemma pi_conj_eq_of_mem_centralizer [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    {c : Ω} (hcB : c ∈ B)
    (hcπ : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) ∈
      Subgroup.centralizer (M.piImg K : Set Γ))
    {y : Ω} (hyK : y ∈ K) (hcyK : c * y * c⁻¹ ∈ K) :
    ((M.π ⟨c * y * c⁻¹, hKS hcyK⟩ : ↥G₀) : Γ) = ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) := by
  have hconj := M.conj ⟨c⁻¹, B.inv_mem hcB⟩ ⟨y, hKS hyK⟩
    ⟨c * y * c⁻¹, hKS hcyK⟩ (by simp)
  have hβ : ((M.β ⟨c⁻¹, B.inv_mem hcB⟩ : ↥Ghat) : Γ) =
      ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ)⁻¹ := by
    have h1 : (⟨c⁻¹, B.inv_mem hcB⟩ : ↥B) = (⟨c, hcB⟩ : ↥B)⁻¹ := by
      ext
      simp
    rw [h1, map_inv]
    rfl
  rw [hβ, inv_inv] at hconj
  have hπy : ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) ∈ M.piImg K :=
    Subgroup.mem_map_of_mem G₀.subtype
      (Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 hyK))
  have hcomm : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) * ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) =
      ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) * ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) :=
    (Subgroup.mem_centralizer_iff.1 hcπ _ hπy).symm
  have hgoal : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) * ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) *
        ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ)⁻¹ = ((M.π ⟨y, hKS hyK⟩ : ↥G₀) : Γ) := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hconj.trans hgoal

private lemma centralizes_K_of_centralizes_piImg [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat)
    (hKnorm : B ≤ Subgroup.normalizer (K : Set Ω)) {c : Ω} (hcB : c ∈ B)
    (hcπ : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) ∈
      Subgroup.centralizer (M.piImg K : Set Γ)) :
    c ∈ Subgroup.centralizer (K : Set Ω) := by
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  haveI : Group.IsPerfect ↥K := isPerfect_K hcfg
  have hcyK : ∀ y ∈ K, c * y * c⁻¹ ∈ K := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 (hKnorm hcB) y).1 hy
  let φ : ↥K →* ↥S :=
    { toFun := fun y => ⟨c * (y : Ω) * c⁻¹, hKS (hcyK y y.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  let ψ : ↥K →* ↥S := Subgroup.inclusion hKS
  have hφψ : ∀ y : ↥K, M.π (φ y) = M.π (ψ y) := by
    intro y
    have hsub : (φ y : ↥S) = ⟨c * (y : Ω) * c⁻¹, hKS (hcyK (y : Ω) y.2)⟩ := rfl
    have hsub2 : (ψ y : ↥S) = ⟨(y : Ω), hKS y.2⟩ := rfl
    rw [hsub, hsub2]
    exact Subtype.ext (pi_conj_eq_of_mem_centralizer hcfg M hKS hcB hcπ y.2
      (hcyK (y : Ω) y.2))
  have hφid : φ = ψ :=
    CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center (p := M.π)
      (by rw [M.ker_π]) hφψ
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : c * y * c⁻¹ = y := by
    have h := congrArg (fun f : ↥K →* ↥S => ((f ⟨y, hy⟩ : ↥S) : Ω)) hφid
    simpa [φ, ψ, Subgroup.coe_inclusion] using h
  calc y * c = (c * y * c⁻¹) * c := by rw [hy']
    _ = c * y := by group

private lemma mem_centralizer_of_mem_mapToPiImg_ker [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) {X : Subgroup Ω}
    (hXS : X ≤ S) {u : ↥X} (hu : u ∈ (mapToPiImg M X hXS).ker) :
    ((u : Ω)) ∈ Subgroup.centralizer (S : Set Ω) := by
  have huπ : M.π ⟨(u : Ω), hXS u.2⟩ = 1 := by
    have h1 : ((M.π ⟨(u : Ω), hXS u.2⟩ : ↥G₀) : Γ) = 1 := by
      have h2 := congrArg (fun z : ↥(M.piImg X) => (z : Γ)) (MonoidHom.mem_ker.1 hu)
      simpa [mapToPiImg] using h2
    exact Subtype.ext h1
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hcen : (⟨(u : Ω), hXS u.2⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [← M.ker_π, MonoidHom.mem_ker]
    exact huπ
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨s, hs⟩)

private lemma not_dvd_card_ker_mapToPiImg [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1) :
    ¬ p ∣ Nat.card ↥(mapToPiImg M K hKS).ker := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  intro hdiv
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hyπ : (y : ↥K) ∈ (mapToPiImg M K hKS).ker := y.2
  have hycen : ((y : ↥K) : Ω) ∈ Subgroup.centralizer (S : Set Ω) :=
    mem_centralizer_of_mem_mapToPiImg_ker hcfg M hKS hyπ
  have hyp : ((y : ↥K) : Ω) ^ p = 1 := by
    have h1 : (y : ↥K) ^ p = 1 := by
      have h2 : orderOf (y : ↥K) = p := by
        rw [Subgroup.orderOf_coe]
        exact hyord
      rw [← h2]
      exact pow_orderOf_eq_one _
    exact congrArg (fun z : ↥K => ((z : Ω))) h1
  have hy1 : ((y : ↥K) : Ω) = 1 := hKZ _ (y : ↥K).2 hycen hyp
  have hy1' : (y : ↥K) = 1 := Subtype.ext hy1
  have h2 : orderOf (y : ↥K) = p := by
    rw [Subgroup.orderOf_coe]
    exact hyord
  rw [hy1', orderOf_one] at h2
  exact hcfg.prime.ne_one h2.symm

private lemma pLift_high_case [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    {kbar : Γ} (hkbar : kbar ∈ M.piImg K)
    (hkp : ((⟨kbar, hkbar⟩ : ↥(M.piImg K)) ^ p = 1))
    {k₁ : ↥K} (hmap : mapToPiImg M K hKS k₁ = ⟨kbar, hkbar⟩)
    {c : ℕ} (ha : orderOf k₁ = p ^ (c + 2)) : False := by
  set u : ↥K := k₁ ^ p ^ (c + 1) with hu
  have hu_ker : u ∈ (mapToPiImg M K hKS).ker := by
    rw [MonoidHom.mem_ker]
    calc mapToPiImg M K hKS u = mapToPiImg M K hKS k₁ ^ p ^ (c + 1) := by rw [hu, map_pow]
      _ = ⟨kbar, hkbar⟩ ^ p ^ (c + 1) := by rw [hmap]
      _ = 1 := by
          rw [show p ^ (c + 1) = p * p ^ c by rw [pow_succ, Nat.mul_comm],
            pow_mul, hkp, one_pow]
  have hu_cen : ((u : ↥K) : Ω) ∈ Subgroup.centralizer (S : Set Ω) :=
    mem_centralizer_of_mem_mapToPiImg_ker hcfg M hKS hu_ker
  have hu_pow : ((u : ↥K) : Ω) ^ p = 1 := by
    have hup : u ^ p = 1 := by
      rw [hu, ← pow_mul, show p ^ (c + 1) * p = p ^ (c + 2) by rw [← pow_succ]]
      rw [← ha]
      exact pow_orderOf_eq_one k₁
    exact congrArg (fun z : ↥K => ((z : Ω))) hup
  have hu_ne : u ≠ 1 := by
    intro hu1
    have hdvd : orderOf k₁ ∣ p ^ (c + 1) := by
      rw [orderOf_dvd_iff_pow_eq_one, ← hu]
      exact hu1
    have hdvd' : p ^ (c + 2) ∣ p ^ (c + 1) := by
      rw [← ha]
      exact hdvd
    have hlt : p ^ (c + 1) < p ^ (c + 2) :=
      Nat.pow_lt_pow_right hcfg.prime.one_lt (by omega)
    exact absurd (Nat.le_of_dvd (Nat.pow_pos hcfg.prime.pos) hdvd') (by omega)
  exact hu_ne (Subtype.ext (hKZ _ u.2 hu_cen hu_pow))

private lemma pow_eq_one_of_pLift [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    {kbar : Γ} (hkbar : kbar ∈ M.piImg K) (hpow : kbar ^ p = 1)
    {k₁ : ↥K}
    (hmap : mapToPiImg M K hKS k₁ = ⟨kbar, hkbar⟩)
    (hpowe : ∃ a, orderOf k₁ = p ^ a) :
    ((k₁ : Ω) ^ p = 1) := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hkp : ((⟨kbar, hkbar⟩ : ↥(M.piImg K)) ^ p = 1) := by
    apply Subtype.ext
    simpa using hpow
  obtain ⟨a, ha⟩ := hpowe
  rcases a with _ | _ | c
  · have h1 : k₁ = 1 := by
      rw [← orderOf_eq_one_iff, ha]
      simp
    rw [h1]
    simp
  · have h1 : k₁ ^ p = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ha]
      simp
    exact congrArg (fun z : ↥K => ((z : Ω))) h1
  · exact (pLift_high_case hcfg M hKS hKZ hkbar hkp hmap ha).elim

private lemma exists_pElement_lift_mem_K [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    {kbar : Γ} (hkbar : kbar ∈ M.piImg K) (hpow : kbar ^ p = 1) :
    ∃ k : ↥K, ((M.π ⟨(k : Ω), hKS k.2⟩ : ↥G₀) : Γ) = kbar ∧
      ((k : Ω) ^ p = 1) := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  let πK : ↥K →* ↥(M.piImg K) := mapToPiImg M K hKS
  have hsurj : Function.Surjective πK := mapToPiImg_surjective M K hKS
  have hC : ¬ p ∣ Nat.card ↥πK.ker := not_dvd_card_ker_mapToPiImg hcfg M hKS hKZ
  let kbar' : ↥(M.piImg K) := ⟨kbar, hkbar⟩
  have hord : ∃ n, orderOf kbar' = p ^ n := by
    have h1 : orderOf kbar = orderOf kbar' := Subgroup.orderOf_coe kbar'
    rw [← h1]
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hcfg.prime).1
      (show orderOf kbar ∣ p ^ 1 by simpa using orderOf_dvd_of_pow_eq_one hpow)
    exact ⟨n, hn⟩
  obtain ⟨hmap, hpowe⟩ :=
    CFSG.LieType.CentralExt.pLift_spec hsurj hC hord (u := kbar')
  refine ⟨CFSG.LieType.CentralExt.pLift p πK kbar', ?_, ?_⟩
  · exact congrArg (fun z : ↥(M.piImg K) => (z : Γ)) hmap
  · exact pow_eq_one_of_pLift hcfg M hKS hKZ hkbar hpow hmap hpowe

private lemma eq_of_pElement_of_mem_K [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    {k₁ k₂ : ↥K}
    (hπ : ((M.π ⟨(k₁ : Ω), hKS k₁.2⟩ : ↥G₀) : Γ) =
      ((M.π ⟨(k₂ : Ω), hKS k₂.2⟩ : ↥G₀) : Γ))
    (h1 : (k₁ : Ω) ^ p = 1) (h2 : (k₂ : Ω) ^ p = 1) : k₁ = k₂ := by
  set z : ↥K := k₁ * k₂⁻¹ with hz
  have hzπ : ((M.π ⟨(z : Ω), hKS z.2⟩ : ↥G₀) : Γ) = 1 := by
    have hzG : M.π ⟨(z : Ω), hKS z.2⟩ = 1 := by
      have e : (⟨(z : Ω), hKS z.2⟩ : ↥S) =
          (⟨(k₁ : Ω), hKS k₁.2⟩ : ↥S) * (⟨(k₂ : Ω), hKS k₂.2⟩ : ↥S)⁻¹ := by
        apply Subtype.ext
        simp [hz, Subgroup.coe_mul, Subgroup.coe_inv]
      have hπG : M.π ⟨(k₁ : Ω), hKS k₁.2⟩ = M.π ⟨(k₂ : Ω), hKS k₂.2⟩ := Subtype.ext hπ
      rw [e, map_mul, map_inv, hπG, mul_inv_cancel]
    exact congrArg G₀.subtype hzG
  have hzker : z ∈ (mapToPiImg M K hKS).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hzπ
  have hzcen : (z : Ω) ∈ Subgroup.centralizer (S : Set Ω) :=
    mem_centralizer_of_mem_mapToPiImg_ker hcfg M hKS hzker
  have hzp : (z : Ω) ^ p = 1 := by
    have hk1 : (k₁ : Ω) = (z : Ω) * (k₂ : Ω) := by
      rw [hz]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hcomm : Commute (z : Ω) (k₂ : Ω) :=
      (Subgroup.mem_centralizer_iff.1 hzcen (k₂ : Ω) (hKS k₂.2)).symm
    have hk1pow : (k₁ : Ω) ^ p = (z : Ω) ^ p * (k₂ : Ω) ^ p := by
      calc (k₁ : Ω) ^ p = ((z : Ω) * (k₂ : Ω)) ^ p := by rw [hk1]
        _ = (z : Ω) ^ p * (k₂ : Ω) ^ p := hcomm.mul_pow p
    rw [h2, mul_one] at hk1pow
    exact hk1pow.symm.trans h1
  have hz1 : (z : Ω) = 1 := hKZ (z : Ω) z.2 hzcen hzp
  have hz1' : z = 1 := Subtype.ext hz1
  calc k₁ = k₁ * k₂⁻¹ * k₂ := by group
    _ = z * k₂ := by rw [← hz]
    _ = k₂ := by rw [hz1', one_mul]

private lemma commutes_B_of_pElement_lift [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    (hKnorm : B ≤ Subgroup.normalizer (K : Set Ω))
    {k : ↥K} {kbar : Γ}
    (hkΓ : ((M.π ⟨(k : Ω), hKS k.2⟩ : ↥G₀) : Γ) = kbar)
    (hkp : ((k : Ω) ^ p = 1))
    (hkbarB : kbar ∈ Subgroup.centralizer (M.barB : Set Γ)) :
    ∀ b' ∈ B, b' * (k : Ω) = (k : Ω) * b' := by
  intro b' hb'
  have hk'K : b' * (k : Ω) * b'⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.1 (hKnorm hb') (k : Ω)).1 k.2
  let k' : ↥K := ⟨b' * (k : Ω) * b'⁻¹, hk'K⟩
  have hk'p : (k' : Ω) ^ p = 1 := by
    have hconj : (MulAut.conj b') ((k : Ω) ^ p) = (b' * (k : Ω) * b'⁻¹) ^ p := by
      rw [map_pow]
      rfl
    rw [hkp, map_one] at hconj
    have : (k' : Ω) = b' * (k : Ω) * b'⁻¹ := rfl
    rw [this]
    exact hconj.symm
  have hπk' : ((M.π ⟨(k' : Ω), hKS k'.2⟩ : ↥G₀) : Γ) = kbar := by
    have hb'bar : ((M.β ⟨b', hb'⟩ : ↥Ghat) : Γ) ∈ M.barB :=
      Subgroup.mem_map_of_mem Ghat.subtype (MonoidHom.mem_range.mpr ⟨⟨b', hb'⟩, rfl⟩)
    have hconj := M.conj ⟨b'⁻¹, B.inv_mem hb'⟩ ⟨(k : Ω), hKS k.2⟩
      ⟨(k' : Ω), hKS k'.2⟩ (by simp [k'])
    have hβ : ((M.β ⟨b'⁻¹, B.inv_mem hb'⟩ : ↥Ghat) : Γ) =
        ((M.β ⟨b', hb'⟩ : ↥Ghat) : Γ)⁻¹ := by
      have h1 : (⟨b'⁻¹, B.inv_mem hb'⟩ : ↥B) = (⟨b', hb'⟩ : ↥B)⁻¹ := by
        ext
        simp
      rw [h1, map_inv]
      rfl
    rw [hβ, inv_inv, hkΓ] at hconj
    have hcomm : ((M.β ⟨b', hb'⟩ : ↥Ghat) : Γ) * kbar =
        kbar * ((M.β ⟨b', hb'⟩ : ↥Ghat) : Γ) :=
      Subgroup.mem_centralizer_iff.1 hkbarB _ hb'bar
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at hconj
    exact hconj
  have hk'eq : k' = k :=
    eq_of_pElement_of_mem_K hcfg M hKS hKZ (hπk'.trans hkΓ.symm) hk'p hkp
  have : b' * (k : Ω) * b'⁻¹ = (k : Ω) := congrArg (fun u : ↥K => (u : Ω)) hk'eq
  calc b' * (k : Ω) = (b' * (k : Ω) * b'⁻¹) * b' := by group
    _ = (k : Ω) * b' := by rw [this]

private lemma mem_B_of_pElement_commutes [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {k : ↥K} (hkp : ((k : Ω) ^ p = 1))
    (hcommB : ∀ b' ∈ B, b' * (k : Ω) = (k : Ω) * b') :
    (k : Ω) ∈ B := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hkelem : (k : Ω) ∈ (B ⊔ Subgroup.zpowers (k : Ω) : Subgroup Ω) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers (k : Ω))
  have hBelem : IsElemAbelian p (B ⊔ Subgroup.zpowers (k : Ω)) := by
    refine IsElemAbelian.sup_of_commute hcfg.elem (isElemAbelian_zpowers hkp) ?_
    intro a ha z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (show Commute a (k : Ω) from hcommB a ha).zpow_right n
  obtain ⟨T, hTS, hT2, hTnorm, hTne⟩ := hcfg.hc
  have hTne' : T ≠ ⊥ := by
    intro hT
    apply hTne
    rw [hT]
    simp
  have hKle : K ≤ closureIn K N := le_closureIn_self K N
  have hEnorm : B ⊔ Subgroup.zpowers (k : Ω) ≤ Subgroup.normalizer (T : Set Ω) := by
    refine sup_le ((le_sup_right : B ≤ closureIn K N ⊔ B).trans hTnorm) ?_
    refine Subgroup.zpowers_le.2 ?_
    exact (hKle.trans le_sup_left).trans (hTnorm.trans (le_refl _)) k.2
  obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥(B ⊔ Subgroup.zpowers (k : Ω)) = p ^ m :=
    hBelem.isPGroup.exists_card_eq
  have hmle : m ≤ CFSG.Open.twoLocalPrimeRank p Ω :=
    le_twoLocalPrimeRank_of_normalizer hcfg.prime hTne' hT2 hBelem hm hEnorm
  have hcardB : Nat.card B = p ^ CFSG.Open.twoLocalPrimeRank p Ω := hcfg.bmax.2.1
  have hcard_le : Nat.card ↥(B ⊔ Subgroup.zpowers (k : Ω)) ≤ Nat.card B := by
    rw [hm, hcardB]
    exact Nat.pow_le_pow_right hcfg.prime.pos hmle
  have hBeq : B = B ⊔ Subgroup.zpowers (k : Ω) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcard_le
  rw [hBeq]
  exact hkelem

private lemma mem_sup_inf_centralizer_of_pElement [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKnorm : B ≤ Subgroup.normalizer (K : Set Ω))
    {b : Ω} (hb : b ∈ B) {k : ↥K} (hkB : (k : Ω) ∈ B)
    {kbar : Γ} (hkΓ : ((M.π ⟨(k : Ω), hKS k.2⟩ : ↥G₀) : Γ) = kbar)
    (hkbarB : kbar ∈ Subgroup.centralizer (M.barB : Set Γ))
    (hrestcent : ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) * kbar⁻¹ ∈
      Subgroup.centralizer (M.piImg K : Set Γ)) :
    b ∈ (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set Ω)) := by
  have hβk : ((M.β ⟨(k : Ω), hkB⟩ : ↥Ghat) : Γ) = kbar := by
    have h1 := M.coe_β_eq_coe_π
      (b := ⟨(k : Ω), hkB⟩) (s := ⟨(k : Ω), hKS k.2⟩) rfl
    exact h1.trans hkΓ
  let c : Ω := (k : Ω)⁻¹ * b
  have hcB : c ∈ B := B.mul_mem (B.inv_mem hkB) hb
  have hβc : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) = kbar⁻¹ * ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) := by
    have h1 : (⟨c, hcB⟩ : ↥B) = (⟨(k : Ω), hkB⟩ : ↥B)⁻¹ * ⟨b, hb⟩ := by
      ext
      simp [c]
    rw [h1, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hβk]
  have hcπ : ((M.β ⟨c, hcB⟩ : ↥Ghat) : Γ) ∈
      Subgroup.centralizer (M.piImg K : Set Γ) := by
    rw [hβc]
    have hcomm : kbar * ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) =
        ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) * kbar :=
      (Subgroup.mem_centralizer_iff.1 hkbarB _ (by
        exact Subgroup.mem_map_of_mem Ghat.subtype
          (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩))).symm
    have hswap : kbar⁻¹ * ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) =
        ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) * kbar⁻¹ := by
      calc kbar⁻¹ * ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ)
          = kbar⁻¹ * (((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) * kbar) * kbar⁻¹ := by group
        _ = kbar⁻¹ * (kbar * ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ)) * kbar⁻¹ := by rw [← hcomm]
        _ = ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) * kbar⁻¹ := by group
    rw [hswap]
    exact hrestcent
  have hccen : c ∈ Subgroup.centralizer (K : Set Ω) :=
    centralizes_K_of_centralizes_piImg hcfg M hKnorm hcB hcπ
  have hb_eq : b = (k : Ω) * c := by
    rw [show c = (k : Ω)⁻¹ * b from rfl]
    group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup
    (Subgroup.mem_inf.2 ⟨hkB, k.2⟩)
    (Subgroup.mem_inf.2 ⟨hcB, hccen⟩)

theorem S172DModel.le_inf_sup_inf_centralizer_of_inner [Finite Ω] {p : ℕ}
    {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hKZ : ∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ p = 1 → k = 1)
    (hinner : ∀ a ∈ M.barB, ∃ k ∈ M.piImg K, k ^ p = 1 ∧
      k ∈ Subgroup.centralizer (M.barB : Set Γ) ∧
      a * k⁻¹ ∈ Subgroup.centralizer (M.piImg K : Set Γ)) :
    B ≤ (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set Ω)) := by
  classical
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hKnorm : B ≤ Subgroup.normalizer (K : Set Ω) := B_le_normalizer_K hcfg
  intro b hb
  have hbbar : ((M.β ⟨b, hb⟩ : ↥Ghat) : Γ) ∈ M.barB :=
    Subgroup.mem_map_of_mem Ghat.subtype (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩)
  obtain ⟨kbar, hkbar, hkbarp, hkbarcent, hrestcent⟩ := hinner _ hbbar
  obtain ⟨k, hkΓ, hkp⟩ := exists_pElement_lift_mem_K hcfg M hKS hKZ hkbar hkbarp
  have hkbarB : kbar ∈ Subgroup.centralizer (M.barB : Set Γ) := hkbarcent
  have hcommB := commutes_B_of_pElement_lift hcfg M hKS hKZ hKnorm hkΓ hkp hkbarB
  have hkB := mem_B_of_pElement_commutes hcfg hkp hcommB
  exact mem_sup_inf_centralizer_of_pElement hcfg M hKS hKnorm hb hkB hkΓ hkbarB hrestcent

private lemma exists_twoElement_pow_of_even_order {G : Type*} [Group G] [Finite G] {s : G}
    (hdvd : 2 ∣ orderOf s) :
    ∃ m, (s ^ m) ^ 2 = 1 ∧ s ^ m ≠ 1 := by
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hm
      exact absurd hm (orderOf_pos s).ne'
    · exact h
  refine ⟨m, ?_, ?_⟩
  · rw [← pow_mul, show m * 2 = orderOf s by omega, pow_orderOf_eq_one]
  · intro h
    have hdvd' : orderOf s ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
    have := Nat.le_of_dvd hmpos hdvd'
    omega

theorem S172DModel.exists_twoGroup_le_of_two_dvd_card_piImg [Finite Ω] {p : ℕ}
    {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) (hKS : K ≤ S)
    (hK2 : 2 ∣ Nat.card (M.piImg K)) :
    ∃ U : Subgroup Ω, U ≤ K ∧ U ≠ ⊥ ∧ IsPGroup 2 U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(M.piImg K) :=
    Finite.of_surjective (mapToPiImg M K hKS) (mapToPiImg_surjective M K hKS)
  obtain ⟨r, hr2⟩ := exists_prime_orderOf_dvd_card' 2 hK2
  obtain ⟨g, hg, hgΓ⟩ := Subgroup.mem_map.1 r.2
  obtain ⟨s, hs, hsπ⟩ := Subgroup.mem_map.1 hg
  have hsK : (s : Ω) ∈ K := (Subgroup.mem_subgroupOf (H := K) (K := S)).1 hs
  have hrΓ : orderOf ((r : ↥(M.piImg K)) : Γ) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hr2
  have hgΓord : orderOf ((g : ↥G₀) : Γ) = 2 := by
    have h := congrArg orderOf hgΓ
    exact h.trans hrΓ
  have hgord : orderOf g = 2 := by
    rw [← Subgroup.orderOf_coe (H := G₀) g]
    exact hgΓord
  have hπs : M.π s = g := hsπ
  have hdvd : 2 ∣ orderOf s := by
    rw [← hgord, ← hπs]
    exact orderOf_map_dvd M.π s
  obtain ⟨m, hu2, hum⟩ := exists_twoElement_pow_of_even_order hdvd
  let u : Ω := (s : Ω) ^ m
  have huΩ : u ^ 2 = 1 := by
    have := congrArg (fun w : ↥S => ((w : Ω))) hu2
    simpa [u, Subgroup.coe_pow] using this
  have hu1 : u ≠ 1 := by
    intro h
    apply hum
    apply Subtype.ext
    simpa [u] using h
  refine ⟨Subgroup.zpowers u, Subgroup.zpowers_le.2 (K.pow_mem hsK m), ?_, ?_⟩
  · intro hbot
    exact hu1 (by simpa [hbot] using Subgroup.mem_zpowers u)
  · exact (isElemAbelian_zpowers huΩ).isPGroup


end CFSG.LocalAnalysis.GLTheoremA.T173O

end
