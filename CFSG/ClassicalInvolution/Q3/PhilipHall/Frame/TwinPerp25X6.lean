module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3B
public import CFSG.ClassicalInvolution.Asc77.AscCX5
public import CFSG.ClassicalInvolution.Asc77.AscCX8B

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.ClassicalInvolution.Asc77.C25W (InFour mem_zStarOf_centralizer_conj_iff good_of_mem_zpowers
  exists_sq_mem_mod exists_conj_ge_sylow)
open CFSG.ClassicalInvolution.Asc77.C25Y (mem_closure_pair)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement


section SqZ

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def SqZLAt (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : Prop :=
  ∀ {a : G}, a ∈ cA S R R' → a * a = 1 → a ≠ 1 → BadElt z a → ∀ {g x : G},
    g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) → x ∈ Subgroup.centralizer ({a} : Set G) →
    x * x = g * z * g⁻¹ → ∃ h ∈ TwinDisc.coreLayer Ω a, h * z * h⁻¹ = g * z * g⁻¹

@[expose] def P25X_SqZL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂), SqZLAt hyp

theorem sqZLAt_of_layerSq (hT : TwinThmE.T4Supply) (h : P25_SqLayer) : P25X_SqZL := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad g x hgC hxC hxx
  obtain ⟨h₀, hh₀, hh₀z⟩ := sqZL_of_layerSq hyp ha2 ha1 haA hT hbad
    (h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad) hgC hxC hxx
  exact ⟨(h₀ : G), Subgroup.mem_map.mpr ⟨h₀, hh₀, rfl⟩, hh₀z⟩

end SqZ

section Fusion

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem goodFusion_of_placed (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQT : QTFAt hyp) (hSqL : SqZLAt hyp)
    {N : Subgroup G} (hNA : N ≤ cA S R R')
    (hsc : ∀ n ∈ N, ∀ c : G, c * z * c⁻¹ = z → c * n * c⁻¹ ∈ (S : Subgroup G) →
      c * n * c⁻¹ ∈ N)
    (hbad : ∀ n ∈ N, n ≠ 1 → BadElt z n)
    (hgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G)))
    {e : G} (heN : e ∈ N) {g : G} (htC : g * z * g⁻¹ ∈ Subgroup.centralizer ({e} : Set G))
    (htz : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({e} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  classical
  by_cases he1 : e = 1
  · subst he1
    exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr (by group), rfl⟩
  set t₀ := g * z * g⁻¹ with ht₀
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hz2 : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    (z_facts hyp).1
  have heS : e ∈ (S : Subgroup G) := (hNA heN).1
  have het : e * t₀ = t₀ * e := (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
  have hNS : ∀ s ∈ (S : Subgroup G), ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs' n hn
    have hsz : s * z * s⁻¹ = z := by rw [hzS s hs']; group
    exact hsc n hn s hsz (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs' (hNA hn).1)
      (Subgroup.inv_mem _ hs'))
  have hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS s hs')
  have hT2 : IsPGroup 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({t₀} : Set G) : Subgroup G) :=
    S.isPGroup'.to_le inf_le_left
  have hTH : (S : Subgroup G) ⊓ Subgroup.centralizer ({t₀} : Set G) ≤
      Subgroup.centralizer ({t₀} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hSz)
  obtain ⟨Q, hQ, hTQ⟩ := IsSylow2In.exists_ge hT2 hTH
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ.2.1 (hQ.1.trans inf_le_left)
  obtain ⟨c, hc, hcQ⟩ := exists_conj_ge_sylow hSz hQ.2.1 (hQ.1.trans inf_le_right)
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hcz]
      _ = z := by group
  have hconjN : ∀ q ∈ Q, q ∈ N → c⁻¹ * q * c ∈ N := by
    intro q hq hqN
    have h1 := hsc q hqN c⁻¹ hcz' (by simpa using hcQ q hq)
    simpa using h1
  have heQ : e ∈ Q := hTQ ⟨heS, Subgroup.mem_centralizer_singleton_iff.mpr het⟩
  have hzQ : z ∈ Q := hTQ ⟨hzA.1, Subgroup.mem_centralizer_singleton_iff.mpr htz.symm⟩
  have hVz : ∀ y ∈ V, y * z = z * y → y ∈ Q := by
    intro y hy hyz
    have hle : Q ≤ V ⊓ Subgroup.centralizer ({z} : Set G) :=
      le_inf hQV (hQ.1.trans inf_le_right)
    have hVH : V ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.centralizer ({t₀} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
      inf_le_inf_right _ hV.1
    have heq := hQ.2.2 _ hVH (hV.2.1.to_le inf_le_left) hle
    rw [← heq]
    exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩
  set B : Subgroup G := conjSub c N ⊓ Q with hB
  have hfwd : ∀ q ∈ Q, ∀ b ∈ B, q * b * q⁻¹ ∈ B := by
    intro q hq b hb
    refine ⟨?_, Q.mul_mem (Q.mul_mem hq hb.2) (Q.inv_mem hq)⟩
    show q * b * q⁻¹ ∈ conjSub c N
    rw [mem_conjSub_iff]
    have h1 := hNS _ (hcQ q hq) _ (mem_conjSub_iff.mp hb.1)
    have e1 : c⁻¹ * (q * b * q⁻¹) * c =
        (c⁻¹ * q * c) * (c⁻¹ * b * c) * (c⁻¹ * q * c)⁻¹ := by group
    rw [e1]
    exact h1
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hfwd q hq b
    · intro hb
      have h1 := hfwd q⁻¹ (Q.inv_mem hq) _ hb
      simpa [mul_assoc] using h1
  have heB : e ∈ B := ⟨mem_conjSub_iff.mpr (hconjN e heQ heN), heQ⟩
  have hB1 : B ≠ ⊥ := by
    intro h
    apply he1
    rw [h, Subgroup.mem_bot] at heB
    exact heB
  obtain ⟨d, hdB, hd1, hd2, hdQ⟩ := CX.exists_central_involution hQ.2.1 inf_le_right hQB hB1
  have hdQ' : d ∈ Q := hdB.2
  set d' := c⁻¹ * d * c with hd'
  have hd'N : d' ∈ N := mem_conjSub_iff.mp hdB.1
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hd1
    calc d = c * d' * c⁻¹ := by rw [hd']; group
      _ = 1 := by rw [h]; group
  have hd'2 : d' * d' = 1 := by
    calc d' * d' = c⁻¹ * (d * d) * c := by rw [hd']; group
      _ = 1 := by rw [hd2]; group
  have hd'A := hNA hd'N
  have hd'bad := hbad d' hd'N hd'1
  have hdzgood : z ∈ zStarOf (Subgroup.centralizer ({d * z} : Set G)) := by
    have e1 : d * z = c * (d' * z) * c⁻¹ := by
      calc d * z = d * (c * z * c⁻¹) := by rw [hcz]
        _ = c * (d' * z) * c⁻¹ := by rw [hd']; group
    rw [e1]
    exact (mem_zStarOf_centralizer_conj_iff hcz).mpr (hgood d' hd'N hd'1)
  have hdz : d ≠ z := by
    intro h
    apply hd'bad
    have e1 : d' = z := by
      rw [hd', h]
      simpa using hcz'
    rw [e1]
    exact T7T.mem_zStarOf_centralizer_self z
  have hdzc : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp ((hQ.1 hdQ').2)
  set U : Subgroup G := Subgroup.closure ({d, z} : Set G) with hU
  have hUE : IsElemAbelian2 U 2 := T7A.isElemAbelian2_closure_pair hd2 hz2 hd1 hz1 hdz hdzc
  have hdU : d ∈ U := Subgroup.subset_closure (by simp)
  have hzV : z ∈ V := hQV hzQ
  have hUV : U ≤ V := by
    rw [hU, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hQV hdQ'
    · exact hzV
  have hΓ : gamma1 U (V ⊓ ⨆ L ∈ twinSet Ω (conjSub g K), L) ≤
      Subgroup.centralizer ({d} : Set G) := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    intro y hy
    obtain ⟨⟨hyV, -⟩, hyw⟩ := (Subgroup.mem_inf.mp hy) |>.imp Subgroup.mem_inf.mp id
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyw' : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hyw
    rcases mem_closure_pair hd2 hz2 hdzc hw with h1 | h1 | h1 | h1
    · exact absurd h1 hw1
    · rw [h1] at hyw'
      exact hyw'
    · rw [h1] at hyw'
      exact hdQ y (hVz y hyV hyw')
    · rw [h1] at hyw'
      have hzdz : z * (d * z) = (d * z) * z := by
        calc z * (d * z) = (z * d) * z := by group
          _ = (d * z) * z := by rw [hdzc]
      exact hdQ y (hVz y hyV (CX.comm_of_mem_zStarOf hV.2.1 hzV hyV hdzgood hzdz hyw'))
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hst.mem
  have htJ : IsUniqueInvolution (conjSub g K) t₀ := hz.conj g
  have hP : PartIHyp Ω := ⟨hΩ, hst.cls, hst.aEmpty⟩
  obtain ⟨x, hxJ, hx4, hxd⟩ := CFSG.ClassicalInvolution.Q3.Q3CL.l9_3 hP (conjSub g K) hJ t₀ htJ V hV U
    hUV hUE d hdU hd1 hΓ
  have hxx : x * x = t₀ := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.sq_eq_of_orderOf_four htJ hxJ hx4
  have hx4' : x * x * x * x = 1 := by
    have h1 : x ^ 4 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx4] at this
    calc x * x * x * x = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := h1
  have hcent := Subgroup.mem_centralizer_iff.mp hd'A.2
  have hd'R : ∀ r ∈ R, d' * r = r * d' := fun r hr => (hcent r (Subgroup.mem_sup_left hr)).symm
  have hd'R' : ∀ r ∈ R', d' * r = r * d' := fun r hr =>
    (hcent r (Subgroup.mem_sup_right hr)).symm
  have hdt : d * t₀ = t₀ * d := Subgroup.mem_centralizer_singleton_iff.mp ((hQ.1 hdQ').1)
  have ht'eq : (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ = c⁻¹ * t₀ * c := by rw [ht₀]; group
  have ht'C : (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ ∈ Subgroup.centralizer ({d'} : Set G) := by
    rw [ht'eq, Subgroup.mem_centralizer_singleton_iff, hd']
    calc c⁻¹ * t₀ * c * (c⁻¹ * d * c) = c⁻¹ * (t₀ * d) * c := by group
      _ = c⁻¹ * (d * t₀) * c := by rw [hdt]
      _ = c⁻¹ * d * c * (c⁻¹ * t₀ * c) := by group
  set x' := c⁻¹ * x * c with hx'
  have hx'C : x' ∈ Subgroup.centralizer ({d'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hx', hd']
    calc c⁻¹ * x * c * (c⁻¹ * d * c) = c⁻¹ * (x * d) * c := by group
      _ = c⁻¹ * (d * x) * c := by rw [hxd]
      _ = c⁻¹ * d * c * (c⁻¹ * x * c) := by group
  have hx'x' : x' * x' = (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ := by
    rw [ht'eq, hx', ← hxx]
    group
  have hx'4 : x' * x' * x' * x' = 1 := by
    calc x' * x' * x' * x' = c⁻¹ * (x * x * x * x) * c := by rw [hx']; group
      _ = 1 := by rw [hx4']; group
  obtain ⟨h₀, hh₀Y, hh₀⟩ := hSqL hd'A hd'2 hd'1 hd'bad ht'C hx'C hx'x'
  set e' := c⁻¹ * e * c with he'
  have he'N : e' ∈ N := hconjN e heQ heN
  have he'1 : e' ≠ 1 := by
    intro h
    apply he1
    calc e = c * e' * c⁻¹ := by rw [he']; group
      _ = 1 := by rw [h]; group
  have hed : e * d = d * e := hdQ e heQ
  have he'd' : e' ∈ Subgroup.centralizer ({d'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, he', hd']
    calc c⁻¹ * e * c * (c⁻¹ * d * c) = c⁻¹ * (e * d) * c := by group
      _ = c⁻¹ * (d * e) * c := by rw [hed]
      _ = c⁻¹ * d * c * (c⁻¹ * e * c) := by group
  have he'triv := mem_trivialOnQuot_of_good hyp hQT hd'A hd'2 hd'1 hd'bad (hNA he'N) he'd'
    (hgood e' he'N he'1)
  have he'2 : IsPGroup 2 (Subgroup.zpowers e') :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hNA he'N).1)
  have he'z : e' * z = z * e' := hzS e' (hNA he'N).1
  have he't : e' * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) = ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) * e' := by
    rw [ht'eq, he']
    calc c⁻¹ * e * c * (c⁻¹ * t₀ * c) = c⁻¹ * (e * t₀) * c := by group
      _ = c⁻¹ * (t₀ * e) * c := by rw [het]
      _ = c⁻¹ * t₀ * c * (c⁻¹ * e * c) := by group
  obtain ⟨h₁, hh₁C, hh₁⟩ := CX.exists_conj_mem_centralizer_of_trivialOnQuot he'2 he'triv he'z he't
    hh₀Y hh₀
  refine ⟨c * h₁ * c⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : h₁ * e' = e' * h₁ := Subgroup.mem_centralizer_singleton_iff.mp hh₁C
    rw [he'] at h1
    calc c * h₁ * c⁻¹ * e = c * (h₁ * (c⁻¹ * e * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * e * c) * h₁) * c⁻¹ := by rw [h1]
      _ = e * (c * h₁ * c⁻¹) := by group
  · have hzc : c⁻¹ * z * c = z := by simpa using hcz'
    calc c * h₁ * c⁻¹ * z * (c * h₁ * c⁻¹)⁻¹ = c * h₁ * (c⁻¹ * z * c) * h₁⁻¹ * c⁻¹ := by group
      _ = c * (h₁ * z * h₁⁻¹) * c⁻¹ := by rw [hzc]; group
      _ = c * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) * c⁻¹ := by rw [hh₁]
      _ = t₀ := by rw [ht₀]; group

end Fusion

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
