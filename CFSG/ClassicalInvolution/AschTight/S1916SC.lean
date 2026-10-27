module

public import CFSG.ClassicalInvolution.AschTight.S1916F2b
public import CFSG.ClassicalInvolution.AschTight.S1916Alp
public import CFSG.ClassicalInvolution.AschTight.S1916SCStmt

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.RankTwoShapes

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conjSub_W_le_sec19X [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V) (c s : G)
    (h : conjSub c W ≤ Subgroup.centralizer ({s} : Set G)) : conjSub c W ≤ sec19X K s := by
  have hd := hDT.toSec19Data
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hΩ := conjInvariant_conjClass K
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := S1911.exists_eta hd
  have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
    (hη.1 (S1911.inf_mem_eta hd hη hinv hWη hηS)).1
  have hmem : ∀ A ∈ USet (CoreAssembly.conjClass K), A ≤ Subgroup.centralizer ({s} : Set G) →
      A ≤ sec19X K s := fun A hA hAs =>
    le_iSup₂ (f := fun B (_ : B ∈ {A : Subgroup G | (A ∈ USet (CoreAssembly.conjClass K) ∨
      A ∈ RSet (CoreAssembly.conjClass K)) ∧ A ≤ Subgroup.centralizer ({s} : Set G)}) => B) A
      ⟨Or.inl hA, hAs⟩
  have hWeq : W = (K ⊓ W) ⊔ V := by rw [inf_comm]; exact ef.supU
  have hsup : conjSub c ((K ⊓ W) ⊔ V) = conjSub c (K ⊓ W) ⊔ conjSub c V :=
    Subgroup.map_sup _ _ _
  rw [hWeq, hsup] at h ⊢
  exact sup_le (hmem _ (USet.conj hΩ hU c) (le_sup_left.trans h))
    (hmem _ (USet.conj hΩ hDT.memV c) (le_sup_right.trans h))

theorem mem_sec19X_conj_of_comm [IsSimpleGroup G] (hZ : C19_14ZTmp p f)
    (hd : Sec19Data p f K z S W) (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {g : G}
    (hgS : g * z * g⁻¹ ∈ (S : Subgroup G)) {x : G} (hxA : x ∈ (S : Subgroup G) ⊓ sec19X K z)
    (hxs : x * (g * z * g⁻¹) = (g * z * g⁻¹) * x) : x ∈ sec19X K (g * z * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  have hsX : g * z * g⁻¹ ∈ sec19X K z := hZ G K z S W hd h1 g hgS
  obtain ⟨s, hs⟩ : ∃ s, s = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hs] at hgS hxs hsX ⊢
  have hs2 : s * s = 1 := by
    rw [hs]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hs1 : s ≠ 1 := fun h => hI.ne_one (by
    have e : z = g⁻¹ * s * g := by rw [hs]; group
    rw [e, h]
    group)
  by_cases hsz : s = z
  · rw [hsz]
    exact hxA.2
  have hxs' : x ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxs
  by_cases hsW : s ∈ W
  · have hWs : W ≤ Subgroup.centralizer ({s} : Set G) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (S1911.comm_of_mem hd w hw s hsW)
    have hP : Subgroup.zpowers x ⊔ W = W :=
      eq_W_of_le_centralizer hDT h1 hsW hs2 hs1 hsz
        (S.isPGroup'.to_le (sup_le (Subgroup.zpowers_le.mpr hxA.1) hd.hWS))
        (sup_le (Subgroup.zpowers_le.mpr hxA.2) (S1911.le_sec19X hd))
        (sup_le (Subgroup.zpowers_le.mpr hxs') hWs) le_sup_right
    have hxW : x ∈ W := hP ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have h2 := conjSub_W_le_sec19X hDT 1 s (by rw [conjSub_one]; exact hWs)
    rw [conjSub_one] at h2
    exact h2 hxW
  obtain ⟨a, haX, hau⟩ := exists_conj_mem_W hDT h1 ⟨hgS, hsX⟩ hsW hs2
  obtain ⟨u, hu⟩ : ∃ u, u = a⁻¹ * s * a := ⟨_, rfl⟩
  rw [← hu] at hau
  have hsu : s = a * u * a⁻¹ := by rw [hu]; group
  have hu2 : u * u = 1 := by
    rw [hu]
    calc a⁻¹ * s * a * (a⁻¹ * s * a) = a⁻¹ * (s * s) * a := by group
      _ = 1 := by rw [hs2]; group
  have hu1 : u ≠ 1 := fun h => hs1 (by rw [hsu, h]; group)
  have haz : a * z = z * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (sec19X_le_centralizer K z haX)
  have huz : u ≠ z := fun h => hsz (by rw [hsu, h, haz]; group)
  have hSyl := isSylow2In_W_centralizer hDT h1 hau hu2 hu1 huz
  have hx'X : a⁻¹ * x * a ∈ sec19X K z :=
    (sec19X K z).mul_mem ((sec19X K z).mul_mem ((sec19X K z).inv_mem haX) hxA.2) haX
  have hx'u : a⁻¹ * x * a ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hu]
    calc a⁻¹ * x * a * (a⁻¹ * s * a) = a⁻¹ * (x * s) * a := by group
      _ = a⁻¹ * (s * x) * a := by rw [hxs]
      _ = a⁻¹ * s * a * (a⁻¹ * x * a) := by group
  have hT2 : IsPGroup 2 (Subgroup.zpowers (a⁻¹ * x * a)) := by
    have h3 := (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxA.1)).map
      (MulAut.conj a⁻¹).toMonoidHom
    rw [MonoidHom.map_zpowers] at h3
    have e : (MulAut.conj a⁻¹).toMonoidHom x = a⁻¹ * x * a := by simp
    rwa [e] at h3
  have hx'H : a⁻¹ * x * a ∈ sec19X K z ⊓ Subgroup.centralizer ({u} : Set G) := ⟨hx'X, hx'u⟩
  obtain ⟨V₁, hV₁, hTV₁⟩ := IsSylow2In.exists_ge hT2 (Subgroup.zpowers_le.mpr hx'H)
  obtain ⟨c, hc, hcW⟩ := IsSylow2In.exists_conj hSyl hV₁
  have hxac : x ∈ conjSub (a * c) W := by
    rw [conjSub_mul, hcW, mem_conjSub_iff]
    exact hTV₁ (Subgroup.mem_zpowers _)
  have hWs : conjSub (a * c) W ≤ Subgroup.centralizer ({s} : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have hsac : s = (a * c) * u * (a * c)⁻¹ := by
      calc s = a * u * a⁻¹ := hsu
        _ = a * (c * u * c⁻¹) * a⁻¹ := by rw [hcu]; group
        _ = (a * c) * u * (a * c)⁻¹ := by group
    have h3 := S1911.comm_of_mem hd _ hy u hau
    rw [Subgroup.mem_centralizer_singleton_iff, hsac]
    calc y * ((a * c) * u * (a * c)⁻¹)
        = (a * c) * (((a * c)⁻¹ * y * (a * c)) * u) * (a * c)⁻¹ := by group
      _ = (a * c) * (u * ((a * c)⁻¹ * y * (a * c))) * (a * c)⁻¹ := by rw [h3]
      _ = (a * c) * u * (a * c)⁻¹ * y := by group
  exact conjSub_W_le_sec19X hDT (a * c) s hWs hxac

variable (p f) in
theorem c19_14SC_of (hZ : C19_14ZTmp p f) : C19_14SCTmp p f := by
  intro G _ _ _ K z S W hd h1 x hx g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hs)
  have hsc : fusionStronglyClosed (((S : Subgroup G) ⊓ sec19X K z : Subgroup G) : Set G) S := by
    refine stronglyClosed_of_alperin S inf_le_left fun Q hQ n hn y hy => ?_
    have hyQ : n⁻¹ * y * n ∈ Q := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) y).mp hy.2
      simpa using h2
    refine ⟨hQ.1 hyQ, ?_⟩
    have hzQ := mem_of_isAlperinSubgroup hQ (sd_mem_S hd) hzS
    have hsQ : n * z * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hn z).mp hzQ
    have hsy : y * (n * z * n⁻¹) = (n * z * n⁻¹) * y := by
      have h3 := hzS _ (hQ.1 hyQ)
      calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
        _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [h3]
        _ = (n * z * n⁻¹) * y := by group
    have hmem := mem_sec19X_conj_of_comm hZ hd h1 (hQ.1 hsQ) hy.1 hsy
    have h4 : n⁻¹ * y * n⁻¹⁻¹ ∈ conjSub n⁻¹ (sec19X K (n * z * n⁻¹)) := conj_mem_conjSub hmem
    have h5 : conjSub n⁻¹ (sec19X K (n * z * n⁻¹)) =
        sec19X K (n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹) :=
      conjSub_gammaGen (conjInvariant_conjClass K) n⁻¹ (n * z * n⁻¹)
    rw [h5, inv_inv, show n⁻¹ * (n * z * n⁻¹) * n = z by group] at h4
    exact h4
  have h2 := hsc x hx g⁻¹ (by simpa using hg)
  simpa using h2.2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
