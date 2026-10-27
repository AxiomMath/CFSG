module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMScalar

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Normalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {y : G}
    (hA : y ∈ Subgroup.normalizer (A : Set G)) (hB : y ∈ Subgroup.normalizer (B : Set G)) :
    y ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hA h, hB h]

private theorem pmFus_mem_normalizer_conjSub {D : Subgroup G} {n y : G}
    (hy : y ∈ Subgroup.normalizer (D : Set G)) :
    n * y * n⁻¹ ∈ Subgroup.normalizer ((conjSub n D : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [mem_conjSub_iff, mem_conjSub_iff,
    show n⁻¹ * (n * y * n⁻¹ * w * (n * y * n⁻¹)⁻¹) * n = y * (n⁻¹ * w * n) * y⁻¹ by group]
  exact Subgroup.mem_normalizer_iff.mp hy (n⁻¹ * w * n)

end Normalizer

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_conj_eq_of_comm_one {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) {s : G}
    (hJs : IsUniqueInvolution J s) (hsne : s ≠ z) {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4)
    (hwz : w * z = z * w) :
    ∃ y₀ ∈ Subgroup.centralizer ({z} : Set G), y₀ * t * y₀⁻¹ = s := by
  have hΩ := hd.tight.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hK := CoreAssembly.mem_conjClass_self K
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) := S19T.isPGroup_zpowers_of_orderOf_four hw4
  obtain ⟨V₀, hV₀, hwV₀⟩ := IsSylow2In.exists_ge hw2
    (Subgroup.zpowers_le.mpr ⟨hwJ, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩ :
      Subgroup.zpowers w ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have h4 : 4 ≤ Nat.card ↥V₀ := by
    calc 4 = Nat.card (Subgroup.zpowers w) := by rw [Nat.card_zpowers, hw4]
      _ ≤ Nat.card ↥V₀ := Subgroup.card_le_of_le hwV₀
  have hsV₀ : s ∈ V₀ := S1911.mem_of_le_member hJs (hV₀.1.trans inf_le_left) hV₀.2.1 (by omega)
  have hJK : J ≠ K := by
    intro h
    rw [h] at hJs
    exact hsne ((hI.unique s hJs.mem hJs.sq).resolve_left hJs.ne_one)
  have hV3 : V₀ ∈ USet (CoreAssembly.conjClass K) := by
    rcases Sec6Gen.Pair.six_two hΩ ⟨hK, hJ, hI, hJs, hsne.symm⟩ hV₀ hsV₀ with
      ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · exact hV3
    · exact absurd ((hV₀.1.trans inf_le_right).trans
        (hd.tight.centralizer_le_normalizer_member hK hI))
        (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ hK hJK hV4
          (hV₀.1.trans inf_le_left))
  obtain ⟨c, hcz, hcV₀⟩ := exists_conj_le_of_sylow_le S hd.hSz (hV₀.1.trans inf_le_right) hV₀.2.1
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hU' := S19B.conjSub_mem_USet hΩ.conjInvariant hV3 c
  have hU'J : conjSub c V₀ ≤ conjSub c J := conjSub_mono (hV₀.1.trans inf_le_left)
  rcases hd.invol_eq_or_of_mem_USet hU' hcV₀ (hΩ.conjInvariant c J hJ) hU'J (hJs.conj c) with
    h | h | h
  · exfalso
    apply hsne
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = z := by rw [h, mul_assoc, ← hcz', inv_mul_cancel_left]
  · refine ⟨c⁻¹, Subgroup.inv_mem _ hcz, ?_⟩
    rw [← h]
    group
  ·
    obtain ⟨r, hr, hrt⟩ := hd.exists_conj_eq_mul
    refine ⟨c⁻¹ * r, Subgroup.mul_mem _ (Subgroup.inv_mem _ hcz) (hd.hSz hr.1), ?_⟩
    calc c⁻¹ * r * t * (c⁻¹ * r)⁻¹ = c⁻¹ * (r * t * r⁻¹) * c := by group
      _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [hrt, h]
      _ = s := by group

theorem exists_conj_mem_normalizer {b : G} (hbz : b ∈ Subgroup.centralizer ({z} : Set G))
    (hbt : b ∈ Subgroup.centralizer ({t} : Set G)) (hb2 : IsPGroup 2 (Subgroup.zpowers b)) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      h⁻¹ * b * h ∈ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := hd.toTightSylowDataR.comm_of_mem
  have hzW : z ∈ W := hd.mem_W_z
  have htW : t ∈ W := hd.mem_W
  set H₂ := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hH₂
  have hWH : W ≤ H₂ := fun x hx =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzW),
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx t htW)⟩
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨P, hP, hWP⟩ := IsSylow2In.exists_ge hW2 hWH
  have hPN : P ≤ Subgroup.normalizer (W : Set G) := by
    intro x hxP
    refine mem_normalizer_iff_conjSub_eq.mpr
      (hd.weaklyClosedIn_W.eq_of_le_of_isPGroup hP.2.1 hWP fun y hy => ?_)
    rw [mem_conjSub_iff] at hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact P.mul_mem (P.mul_mem hxP (hWP hy)) (P.inv_mem hxP)
  have hbH : Subgroup.zpowers b ≤ H₂ := Subgroup.zpowers_le.mpr ⟨hbz, hbt⟩
  obtain ⟨h, hh, hle⟩ := Sec7.exists_conj_le_of_isSylow2In hP hb2 hbH
  have hb : b ∈ conjSub h P := hle (Subgroup.mem_zpowers b)
  exact ⟨h, hh, hPN (mem_conjSub_iff.mp hb)⟩

theorem actsPM_of_conj (hr : 4 ≤ r) {x y f : G} (hft : f * t * f⁻¹ = z) (hy : y = f⁻¹ * x * f)
    (hxz : x ∈ Subgroup.centralizer ({z} : Set G))
    (hxU : x ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G))
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyt : y ∈ Subgroup.centralizer ({t} : Set G)) (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (hyU : ActsPM (K ⊓ W) y) : ActsPM (K ⊓ W) x := by
  have hI := hd.tight.isUniqueInvolution
  obtain ⟨c, hc⟩ := CoreAssembly.single_class K L hd.memL
  have hczt : c * z * c⁻¹ = t := by
    have h1 : IsUniqueInvolution L (c * z * c⁻¹) := by
      rw [hc]
      exact hI.conj c
    exact (hd.invL.eq h1).symm
  have hVL : V ≤ L := hd.le_member
  have hWL : W ⊓ L = V := by
    apply le_antisymm
    · intro x' hx'
      rw [← hd.inf_member_eq]
      exact ⟨hd.hWS hx'.1, hx'.2⟩
    · exact le_inf hd.leW hVL
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    hd.tight.centralizer_le_normalizer_member hd.memL hd.invL hyt
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := by
    have h := mem_normalizer_inf_of_mem hyW hyL
    rwa [hWL] at h
  have hV'K : conjSub c⁻¹ V ≤ K := by
    have h := conjSub_mono (n := c⁻¹) hVL
    rwa [hc, conjSub_inv_conjSub] at h
  have hV'c : IsCyclic ↥(conjSub c⁻¹ V) := isCyclic_conjSub hd.isCyclic_V c⁻¹
  have hV'n : Nat.card ↥(conjSub c⁻¹ V) = 2 ^ (r - 1) :=
    (natCard_conjSub V c⁻¹).trans hd.natCard_V
  have hact : ActsPM (conjSub c⁻¹ V) (c⁻¹ * y * c) := by
    have h := (actsPM_conjSub_iff V c⁻¹ y).mpr (hd.actsPM_V_of_actsPM_inf hyz hyt hyW hyU)
    rwa [inv_inv] at h
  have hN : c⁻¹ * y * c ∈ Subgroup.normalizer ((conjSub c⁻¹ V : Subgroup G) : Set G) := by
    have h := pmFus_mem_normalizer_conjSub (n := c⁻¹) hyV
    rwa [inv_inv] at h
  have hgz : f * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hct : c * z = t * c := by rw [← hczt]; group
    have hft' : f * t = z * f := by rw [← hft]; group
    calc f * c * z = f * (c * z) := by group
      _ = f * (t * c) := by rw [hct]
      _ = f * t * c := by group
      _ = z * f * c := by rw [hft']
      _ = z * (f * c) := by group
  have he : (f * c)⁻¹ * x * (f * c) = c⁻¹ * y * c := by rw [hy]; group
  have hyD : (f * c)⁻¹ * x * (f * c) ∈
      Subgroup.normalizer ((conjSub c⁻¹ V : Subgroup G) : Set G) := by
    rw [he]
    exact hN
  have hact' : ActsPM (conjSub c⁻¹ V) ((f * c)⁻¹ * x * (f * c)) := by
    rw [he]
    exact hact
  exact (hd.actsPM_conj_iff hr inf_le_left hV'K hd.isCyclic_inf hV'c hd.natCard_inf_W hV'n hgz
    hxz hxU hyD).mpr hact'

theorem not_actsPM_conj (hr : 4 ≤ r) {x : G} (hxS : x ∈ (S : Subgroup G)) (hx2 : x * x = 1)
    (hx : x ∉ pmSubgroup (K ⊓ W)) {w₀ : G} (hw₀ : w₀ ∈ (S : Subgroup G) ⊓ K)
    (hw₀x : w₀ * x = x * w₀) (hw₀4 : orderOf w₀ = 4) {g : G}
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G),
      g⁻¹ * y * g ∈ (S : Subgroup G)) : g⁻¹ * x * g ∉ pmSubgroup (K ⊓ W) := by
  intro hb
  have hSz := hd.hSz
  have hI := hd.tight.isUniqueInvolution
  have hzS : z ∈ (S : Subgroup G) := hd.toTightSylowDataR.mem_S
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hSz hxS)
  have hbS : g⁻¹ * x * g ∈ (S : Subgroup G) :=
    hg x ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hsS : g⁻¹ * z * g ∈ (S : Subgroup G) :=
    hg z ⟨hzS, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hw'S : g⁻¹ * w₀ * g ∈ (S : Subgroup G) :=
    hg w₀ ⟨hw₀.1, Subgroup.mem_centralizer_singleton_iff.mpr hw₀x⟩
  have hxU : x ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
    hd.le_normalizer_inf_W hr hxS
  have hbU : g⁻¹ * x * g ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
    hd.le_normalizer_inf_W hr hbS
  by_cases hs : g⁻¹ * z * g = z
  ·
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * z = g * (g⁻¹ * z * g) := by rw [hs]
        _ = z * g := by group
    exact hx ((hd.actsPM_conj_iff_inf hr hgz (hSz hxS) hxU hbU).mpr hb)
  ·
    have hΩ := hd.tight.hypGen
    have hJ : conjSub g⁻¹ K ∈ CoreAssembly.conjClass K :=
      hΩ.conjInvariant g⁻¹ K (CoreAssembly.mem_conjClass_self K)
    have hJs : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
      have h := hI.conj g⁻¹
      rwa [inv_inv] at h
    have hwJ : g⁻¹ * w₀ * g ∈ conjSub g⁻¹ K := by
      have h := conj_mem_conjSub (n := g⁻¹) hw₀.2
      rwa [inv_inv] at h
    have hw4 : orderOf (g⁻¹ * w₀ * g) = 4 := by
      rw [← hw₀4]
      exact (SemiconjBy.orderOf_eq g⁻¹ (by unfold SemiconjBy; group)).symm
    have hwz : g⁻¹ * w₀ * g * z = z * (g⁻¹ * w₀ * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hSz hw'S)
    obtain ⟨y₀, hy₀z, hy₀⟩ := hd.exists_conj_eq_of_comm_one hJ hJs hs hwJ hw4 hwz
    obtain ⟨b, hbdef⟩ : ∃ b : G, b = g⁻¹ * x * g := ⟨_, rfl⟩
    rw [← hbdef] at hbS hbU hb
    have hbz : b ∈ Subgroup.centralizer ({z} : Set G) := hSz hbS
    have hbs : b * (g⁻¹ * z * g) = (g⁻¹ * z * g) * b := by
      calc b * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by rw [hbdef]; group
        _ = g⁻¹ * (z * x) * g := by rw [hxz]
        _ = (g⁻¹ * z * g) * b := by rw [hbdef]; group
    have hb2 : b * b = 1 := by
      calc b * b = g⁻¹ * (x * x) * g := by rw [hbdef]; group
        _ = 1 := by rw [hx2]; group
    obtain ⟨b', hb'def⟩ : ∃ b' : G, b' = y₀⁻¹ * b * y₀ := ⟨_, rfl⟩
    have hb'z : b' ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [hb'def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₀z) hbz) hy₀z
    have hb't : b' ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ht' : t = y₀⁻¹ * (g⁻¹ * z * g) * y₀ := by rw [← hy₀]; group
      rw [ht']
      calc b' * (y₀⁻¹ * (g⁻¹ * z * g) * y₀) = y₀⁻¹ * (b * (g⁻¹ * z * g)) * y₀ := by
            rw [hb'def]; group
        _ = y₀⁻¹ * ((g⁻¹ * z * g) * b) * y₀ := by rw [hbs]
        _ = (y₀⁻¹ * (g⁻¹ * z * g) * y₀) * b' := by rw [hb'def]; group
    have hb'2 : b' * b' = 1 := by
      calc b' * b' = y₀⁻¹ * (b * b) * y₀ := by rw [hb'def]; group
        _ = 1 := by rw [hb2]; group
    have hb'P : IsPGroup 2 (Subgroup.zpowers b') :=
      (S19Q.isPGroup_zpowers_iff_exists_pow _).mpr ⟨1, by rw [pow_one, sq, hb'2]⟩
    obtain ⟨h, ⟨hhz, hht⟩, hhW⟩ := hd.exists_conj_mem_normalizer hb'z hb't hb'P
    have hyz : h⁻¹ * b' * h ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhz) hb'z) hhz
    have hyt : h⁻¹ * b' * h ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hht) hb't) hht
    have hq : y₀ * h ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hy₀z hhz
    have hyeq : (y₀ * h)⁻¹ * b * (y₀ * h) = h⁻¹ * b' * h := by rw [hb'def]; group
    have hyU' : h⁻¹ * b' * h ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (by rw [hd.tight.normEq]; exact hyz) hhW
    have hyAct : ActsPM (K ⊓ W) (h⁻¹ * b' * h) := by
      have := (hd.actsPM_conj_iff_inf hr hq hbz hbU (by rw [hyeq]; exact hyU')).mp hb
      rwa [hyeq] at this
    have hft : (g * y₀ * h) * t * (g * y₀ * h)⁻¹ = z := by
      have hht' : h * t * h⁻¹ = t := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hht, mul_inv_cancel_right]
      calc (g * y₀ * h) * t * (g * y₀ * h)⁻¹ = g * y₀ * (h * t * h⁻¹) * y₀⁻¹ * g⁻¹ := by group
        _ = g * (y₀ * t * y₀⁻¹) * g⁻¹ := by rw [hht']; group
        _ = z := by rw [hy₀]; group
    have hyf : h⁻¹ * b' * h = (g * y₀ * h)⁻¹ * x * (g * y₀ * h) := by
      rw [hb'def, hbdef]; group
    exact hx (hd.actsPM_of_conj hr hft hyf (hSz hxS) hxU hyz hyt hhW hyAct)

theorem hfus (hr : 4 ≤ r) {x : G} (hxS : x ∈ (S : Subgroup G)) (hx2 : x * x = 1)
    (hx : x ∉ pmSubgroup (K ⊓ W)) {w₀ : G} (hw₀ : w₀ ∈ (S : Subgroup G) ⊓ K)
    (hw₀x : w₀ * x = x * w₀) (hw₀4 : orderOf w₀ = 4) (g : G)
    (hg : ∀ y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G),
      g⁻¹ * y * g ∈ (S : Subgroup G)) : x⁻¹ * (g⁻¹ * x * g) ∈ pmSubgroup (K ⊓ W) := by
  have hb := hd.not_actsPM_conj hr hxS hx2 hx hw₀ hw₀x hw₀4 hg
  have hbS : g⁻¹ * x * g ∈ (S : Subgroup G) :=
    hg x ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hb2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  exact inv_mul_mem_pmSubgroup_of_involution hd.isCyclic_inf (n := r - 1) (by omega)
    hd.natCard_inf_W (hd.le_normalizer_inf_W hr hxS) (hd.le_normalizer_inf_W hr hbS) hx2 hb2 hx hb

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
