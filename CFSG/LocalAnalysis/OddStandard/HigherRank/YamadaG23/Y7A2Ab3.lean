module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma mem_conjSub {Y : Subgroup G} {c x : G} :
    x ∈ conjSub c Y ↔ ∃ y ∈ Y, c * y * c⁻¹ = x := by
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem y7a_central_of_k {M I B V E F W : Subgroup G} {k : G}
    (hMIB : M ≤ I ⊔ B) (hIM : I ≤ M) (hBM : B ≤ M) (hVI : V ≤ I)
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x) (hFI : F ≤ I) (hWF : W ≤ F) (hWV : W ≤ V)
    (hWM : ∀ x ∈ M, ∀ w ∈ W, x * w = w * x)
    (hcI : Nat.card ↥I = 32) (hcV : Nat.card ↥V = 16) (hcW : Nat.card ↥W = 4)
    (hVF : V ⊓ F ≤ W) (hVE : ∀ v ∈ V, ∀ e ∈ E, v * e = e * v)
    (hVF' : ∀ v ∈ V, ∀ f ∈ F, v * f = f * v)
    (hZV : ∀ x ∈ M, (∀ y ∈ M, x * y = y * x) → x ∈ V)
    (hkM : ∀ x ∈ M, k * x * k⁻¹ ∈ M) (hkI : ∀ x ∈ I, k * x * k⁻¹ ∈ I)
    (hkW : ∀ w ∈ W, k * w * k⁻¹ ∈ W) (hk3 : k ^ 3 = 1)
    (hfpf : ∀ x ∈ I, k * x * k⁻¹ * x⁻¹ ∈ F → x ∈ F)
    (hBgen : B ≤ F ⊔ E ⊔ conjSub k E) :
    ∀ x ∈ M, ∀ v ∈ V, x * v = v * x := by
  have hkinv : k⁻¹ = k * k := by
    have h : k * k ^ 2 = 1 := by
      rw [← pow_succ', hk3]
    have := inv_eq_of_mul_eq_one_right h
    simpa [pow_two] using this
  have hkinv2 : k⁻¹ * k⁻¹ = k := by
    rw [← mul_inv_rev, ← hkinv, inv_inv]
  have hconj_inv : ∀ x : G, k⁻¹ * x * k = k * (k * x * k⁻¹) * k⁻¹ := by
    intro x
    rw [show k * (k * x * k⁻¹) * k⁻¹ = (k * k) * x * (k⁻¹ * k⁻¹) by group,
      ← hkinv, hkinv2]
  have hkinvM : ∀ x ∈ M, k⁻¹ * x * k ∈ M := by
    intro x hx
    rw [hconj_inv x]
    exact hkM _ (hkM x hx)
  have hkinvI : ∀ x ∈ I, k⁻¹ * x * k ∈ I := by
    intro x hx
    rw [hconj_inv x]
    exact hkI _ (hkI x hx)
  have hkinvW : ∀ x ∈ W, k⁻¹ * x * k ∈ W := by
    intro x hx
    rw [hconj_inv x]
    exact hkW _ (hkW x hx)
  set Z : Subgroup G := cen M with hZdef
  have hmemZ : ∀ x : G, x ∈ Z ↔ x ∈ M ∧ ∀ y ∈ M, y * x = x * y := by
    intro x
    simp only [hZdef, cen, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hZleV : Z ≤ V := by
    intro x hx
    obtain ⟨hxM, hxc⟩ := (hmemZ x).mp hx
    exact hZV x hxM fun y hy => (hxc y hy).symm
  have hWZ : W ≤ Z := by
    intro w hw
    rw [hmemZ w]
    exact ⟨hIM (hFI (hWF hw)), fun y hy => hWM y hy w hw⟩
  have hkZ : ∀ x ∈ Z, k * x * k⁻¹ ∈ Z := by
    intro x hx
    obtain ⟨hxM, hxc⟩ := (hmemZ x).mp hx
    rw [hmemZ (k * x * k⁻¹)]
    refine ⟨hkM x hxM, fun y hy => ?_⟩
    have hy' : k⁻¹ * y * k ∈ M := hkinvM y hy
    have hcy := hxc (k⁻¹ * y * k) hy'
    calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [hcy]
      _ = (k * x * k⁻¹) * y := by group
  set V' : Subgroup G := conjSub k V with hV'def
  have hV'I : V' ≤ I := by
    intro x hx
    rw [hV'def, mem_conjSub] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hkI y (hVI hy)
  have hcV' : Nat.card ↥V' = 16 := by
    rw [hV'def, conjSub, Subgroup.card_map_of_injective (MulAut.conj k).injective, hcV]
  have hVV'Z : V ⊓ V' ≤ Z := by
    intro v hv
    obtain ⟨hvV, hvV'⟩ := Subgroup.mem_inf.mp hv
    rw [hV'def, mem_conjSub] at hvV'
    obtain ⟨v', hv'V, rfl⟩ := hvV'
    have hvI : k * v' * k⁻¹ ∈ I := hkI v' (hVI hv'V)
    have hcent : M ≤ Subgroup.centralizer ({k * v' * k⁻¹} : Set G) := by
      refine le_trans hMIB (sup_le ?_ ?_)
      · intro i hi
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hI _ hvI i hi).symm
      · refine le_trans hBgen (sup_le (sup_le ?_ ?_) ?_)
        · intro f hf
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hVF' _ hvV f hf).symm
        · intro e he
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hVE _ hvV e he).symm
        · intro g hg
          rw [mem_conjSub] at hg
          obtain ⟨e, he, rfl⟩ := hg
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (k * e * k⁻¹) * (k * v' * k⁻¹) = k * (e * v') * k⁻¹ := by group
            _ = k * (v' * e) * k⁻¹ := by rw [← hVE v' hv'V e he]
            _ = (k * v' * k⁻¹) * (k * e * k⁻¹) := by group
    rw [hmemZ (k * v' * k⁻¹)]
    refine ⟨hkM v' (hIM (hVI hv'V)), fun y hy => ?_⟩
    have hyc := hcent hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc
  have hrelV : V.relIndex I = 2 := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := I)
    rw [inf_of_le_left hVI, hcV, hcI] at h
    omega
  have hrelV' : V'.relIndex I = 2 := by
    have h := Subgroup.relIndex_mul_card (H := V') (K := I)
    rw [inf_of_le_left hV'I, hcV', hcI] at h
    omega
  have hrelinf : (V ⊓ V').relIndex I ≤ 4 := by
    have h := Subgroup.relIndex_inf_le (H := V) (K := V') (L := I)
    rw [hrelV, hrelV'] at h
    omega
  have hcardVV' : (V ⊓ V').relIndex I * Nat.card ↥(V ⊓ V') = 32 := by
    have h := Subgroup.relIndex_mul_card (H := V ⊓ V') (K := I)
    rw [inf_of_le_left (le_trans inf_le_left hVI), hcI] at h
    exact h
  have hge8 : 8 ≤ Nat.card ↥(V ⊓ V') := by
    have h := Nat.mul_le_mul_right (Nat.card ↥(V ⊓ V')) hrelinf
    omega
  have hge8Z : 8 ≤ Nat.card ↥Z := by
    have h := Subgroup.card_le_of_le hVV'Z
    omega
  have hZle16 : Nat.card ↥Z ≤ 16 := by
    have h := Subgroup.card_le_of_le hZleV
    rwa [hcV] at h
  have hZdvd : Nat.card ↥Z ∣ 2 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hZleV
    rw [hcV] at h
    simpa using h
  have hZcases : Nat.card ↥Z = 8 ∨ Nat.card ↥Z = 16 := by
    obtain ⟨n, hn, hnc⟩ := (Nat.dvd_prime_pow (p := 2) (m := 4) Nat.prime_two).mp hZdvd
    have h8 : 8 ≤ 2 ^ n := by simpa [hnc] using hge8Z
    have h16 : 2 ^ n ≤ 16 := by simpa [hnc] using hZle16
    interval_cases n
    · norm_num at h8
    · norm_num at h8
    · norm_num at h8
    · left; rw [hnc]; norm_num
    · right; rw [hnc]; norm_num
  rcases hZcases with hZ8 | hZ16
  · exfalso
    have hWlt : W < Z := by
      refine lt_of_le_of_ne hWZ ?_
      intro hEq
      rw [← hEq, hcW] at hZ8
      omega
    obtain ⟨x, hxZ, hxW⟩ :=
      Set.exists_of_ssubset (show (W : Set G) ⊂ (Z : Set G) from hWlt)
    have hxI : x ∈ I := hVI (hZleV hxZ)
    have hkxZ : k * x * k⁻¹ ∈ Z := hkZ x hxZ
    have hkxW : k * x * k⁻¹ ∉ W := by
      intro h
      have h2 : k⁻¹ * (k * x * k⁻¹) * k ∈ W := hkinvW _ h
      have h3 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [h3] at h2
      exact hxW h2
    have hWrel : W.relIndex Z = 2 := by
      have h := Subgroup.relIndex_mul_card (H := W) (K := Z)
      rw [inf_of_le_left hWZ, hcW, hZ8] at h
      omega
    have hxkxW : x⁻¹ * (k * x * k⁻¹) ∈ W := by
      obtain ⟨a, haZ, haW, hall⟩ :=
        (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := W) (K := Z)).mp hWrel
      have hax : a * x ∈ W := (hall x hxZ).resolve_right hxW
      have hakx : a * (k * x * k⁻¹) ∈ W := (hall _ hkxZ).resolve_right hkxW
      have heq : x⁻¹ * (k * x * k⁻¹)
          = (a * x)⁻¹ * (a * (k * x * k⁻¹)) := by
        calc x⁻¹ * (k * x * k⁻¹)
            = (a⁻¹ * (a * x))⁻¹ * (a⁻¹ * (a * (k * x * k⁻¹))) := by group
          _ = (a * x)⁻¹ * (a * (k * x * k⁻¹)) := by group
      rw [heq]
      exact mul_mem (inv_mem hax) hakx
    have hxkb : k * x * k⁻¹ * x⁻¹ ∈ W := by
      have hbM : k * x * k⁻¹ ∈ M := hIM (hVI (hZleV hkxZ))
      have hxk : x * (k * x * k⁻¹) = (k * x * k⁻¹) * x :=
        ((hmemZ x).mp hxZ).2 _ hbM |>.symm
      have hcomm : x⁻¹ * (k * x * k⁻¹) = (k * x * k⁻¹) * x⁻¹ := by
        calc x⁻¹ * (k * x * k⁻¹)
            = x⁻¹ * ((k * x * k⁻¹) * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * (k * x * k⁻¹)) * x⁻¹ := by rw [← hxk]
          _ = (k * x * k⁻¹) * x⁻¹ := by group
      rwa [hcomm] at hxkxW
    exact hxW (hVF ⟨hZleV hxZ, hfpf x hxI (hWF hxkb)⟩)
  ·
    have hZVeq : Z = V := Subgroup.eq_of_le_of_card_ge hZleV (by rw [hZ16, hcV])
    intro x hxM v hvV
    have hvZ : v ∈ Z := by rw [hZVeq]; exact hvV
    exact ((hmemZ v).mp hvZ).2 x hxM

end CFSG.OddStandard.HigherRank.YamadaG23
