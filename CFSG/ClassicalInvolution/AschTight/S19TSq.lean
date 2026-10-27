module

public import CFSG.ClassicalInvolution.AschTight.S19TSec
public import CFSG.ClassicalInvolution.AschTight.S19TBr3
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.ClassicalInvolution.AschTight.S19B93
public import CFSG.ClassicalInvolution.AschTight.S19TF2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [Finite G] [Fact p.Prime] [IsSimpleGroup G] in
theorem isPGroup_zpowers_of_orderOf_four {w : G} (hw4 : orderOf w = 4) :
    IsPGroup 2 (Subgroup.zpowers w) := by
  refine (isPGroup_zpowers_iff w).mpr ⟨2, ?_⟩
  rw [show 2 ^ 2 = orderOf w by rw [hw4]; norm_num]
  exact pow_orderOf_eq_one w

omit [Finite G] [IsSimpleGroup G] in
theorem exists_conj_of_conj {c x s h' : G} (hcz : c * z = z * c)
    (hh' : h' ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G)) (he : h' * z * h'⁻¹ = c * s * c⁻¹) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hcz' : c * z * c⁻¹ = z := by rw [hcz, mul_inv_cancel_right]
  refine ⟨c⁻¹ * h' * c, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hh' ⊢
    calc c⁻¹ * h' * c * x = c⁻¹ * (h' * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * h') * c := by rw [hh']
      _ = x * (c⁻¹ * h' * c) := by group
  · calc c⁻¹ * h' * c * z * (c⁻¹ * h' * c)⁻¹ = c⁻¹ * (h' * (c * z * c⁻¹) * h'⁻¹) * c := by
          group
      _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [hcz', he]
      _ = s := by group

theorem invol_eq_or_of_mem_USet (hd : Sec19DataT p f K z S W L t V) {U : Subgroup G}
    (hU : U ∈ USet (CoreAssembly.conjClass K)) (hUS : U ≤ (S : Subgroup G)) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) (hUJ : U ≤ J) {u : G} (hu : IsUniqueInvolution J u) :
    u = z ∨ u = t ∨ u = t * z := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have htb := ht.toTightBranch
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := S1911.exists_eta hd0
  obtain ⟨V₀, ⟨hV₀η, hor⟩, -⟩ := l6_8 p f ht.branch.odd ht.branch.five G _ hΩ S _ hU hUS η
    ⟨S', hη, hinv⟩ hηS
  rcases hor with h | h
  · exact S1911.invol_eq_or hd hη hinv hWη hV₀η hJ (h ▸ hUJ) hu
  · obtain ⟨J₂, hJ₂, hRJ₂, -, -⟩ := mem_RSet_iff.mp h
    obtain ⟨j, hj⟩ := S1911.exists_isUniqueInvolution_member htb hJ₂
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet ht.branch.odd hU
    have huU : u ∈ U := S1911.mem_of_le_member hu hUJ (S.isPGroup'.to_le hUS) (by omega)
    have hju : u = j := (hj.unique u (hRJ₂ (Subgroup.mem_sup_left huU)) hu.sq).resolve_left
      hu.ne_one
    exact S1911.invol_eq_or hd hη hinv hWη hV₀η hJ₂ (le_sup_right.trans hRJ₂) (hju ▸ hj)

theorem exists_conj_eq_of_comm (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    {s : G} (hJs : IsUniqueInvolution J s) (hsx : s * x = x * s) (hsne : s ≠ z) {w : G}
    (hwJ : w ∈ J) (hw4 : orderOf w = 4) (hwz : w * z = z * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  have hK := CoreAssembly.mem_conjClass_self K
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) := hd0.hSz hxS
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := S1911.centralizer_le_normalizer_member htb hJ
    hJs (Subgroup.mem_centralizer_singleton_iff.mpr hsx.symm)
  have hxH : x ∈ Subgroup.normalizer
      ((J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyz⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxJ y).mp hyJ,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hxz hyz) (Subgroup.inv_mem _ hxz)⟩
    · rintro ⟨hyJ, hyz⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxJ y).mpr hyJ, ?_⟩
      have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxz) hyz) hxz
      simpa [mul_assoc] using h
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hNH : J ⊓ Subgroup.centralizer ({z} : Set G) ⊔ Subgroup.zpowers x ≤
      Subgroup.normalizer ((J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxH)
  obtain ⟨P, hP, hxP⟩ := IsSylow2In.exists_ge hx2
    (le_sup_right : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({z} : Set G) ⊔ _)
  have hV₀ : IsSylow2In (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)))
      (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    S1916.isSylow2In_inf_of_le_normalizer hP le_sup_left hNH
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_orderOf_four hw4
  obtain ⟨V₁, hV₁, hwV₁⟩ := IsSylow2In.exists_ge hw2
    (Subgroup.zpowers_le.mpr ⟨hwJ, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩ :
      Subgroup.zpowers w ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have h4 : 4 ≤ Nat.card ↥(P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) := by
    rw [IsSylow2In.natCard_eq hV₀ hV₁]
    calc 4 = Nat.card (Subgroup.zpowers w) := by rw [Nat.card_zpowers, hw4]
      _ ≤ Nat.card V₁ := Subgroup.card_le_of_le hwV₁
  have hsV₀ : s ∈ P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    S1911.mem_of_le_member hJs (hV₀.1.trans inf_le_left) hV₀.2.1 (by omega)
  have htwin : J ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, u, hu₁, hu₂⟩
    have e1 := (hI.unique u hu₁.mem hu₁.sq).resolve_left hu₁.ne_one
    have e2 := (hJs.unique u hu₂.mem hu₂.sq).resolve_left hu₂.ne_one
    exact hsne (e2.symm.trans e1)
  have hJK : J ≠ K := by
    rintro rfl
    exact htwin ⟨hJ, z, hI, hI⟩
  have hV3 : P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G)) ∈ USet (CoreAssembly.conjClass K) := by
    rcases l6_2 p f hd.tight.branch.odd hd.tight.branch.five G _ hΩ K hK z hI J hJ htwin s hJs
      _ hV₀ hsV₀ with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hJs.sq) hJs.ne_one] at h4
      omega
    · exact hV3
    · exact absurd ((hV₀.1.trans inf_le_right).trans
        (S1911.centralizer_le_normalizer_member htb hK hI))
        (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ hK hJK hV4
          (hV₀.1.trans inf_le_left))
  have hPz : P ≤ Subgroup.centralizer ({z} : Set G) :=
    hP.1.trans (sup_le inf_le_right (Subgroup.zpowers_le.mpr hxz))
  obtain ⟨c, hcz, hcP⟩ := exists_conj_le_of_sylow_le S hd0.hSz hPz hP.2.1
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hcxS : c * x * c⁻¹ ∈ (S : Subgroup G) :=
    hcP (conj_mem_conjSub (hxP (Subgroup.mem_zpowers x)))
  have hx' := conj_mem_sec19BPrime hd hx hcz' hcxS
  have hU' := S19B.conjSub_mem_USet hΩ.conjInvariant hV3 c
  have hU'S : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ (S : Subgroup G) :=
    (conjSub_mono inf_le_left).trans hcP
  have hU'J : conjSub c (P ⊓ (J ⊓ Subgroup.centralizer ({z} : Set G))) ≤ conjSub c J :=
    conjSub_mono (inf_le_right.trans inf_le_left)
  rcases invol_eq_or_of_mem_USet hd hU' hU'S (hΩ.conjInvariant c J hJ) hU'J (hJs.conj c) with
    h | h | h
  · exfalso
    apply hsne
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = z := by rw [h, mul_assoc, ← hcz', inv_mul_cancel_left]
  · obtain ⟨h', hh', he⟩ := exists_conj_eq_t hd hx'
    exact exists_conj_of_conj hcz' hh' (he.trans h.symm)
  · obtain ⟨h', hh', he⟩ := exists_conj_eq_mul_z hd hx'
    exact exists_conj_of_conj hcz' hh' (he.trans h.symm)

theorem exists_conj_eq_of_comm' (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    {s : G} (hJs : IsUniqueInvolution J s) (hsx : s * x = x * s) {h₀ m : G}
    (hh₀ : h₀ ∈ Subgroup.centralizer ({x} : Set G)) (hm : h₀ * z * h₀⁻¹ = m) (hsne : s ≠ m)
    {w : G} (hwJ : w ∈ J) (hw4 : orderOf w = 4) (hwm : w * m = m * w) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = s := by
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hh₀x : h₀ * x = x * h₀ := Subgroup.mem_centralizer_singleton_iff.mp hh₀
  have hJs₁ : IsUniqueInvolution (conjSub h₀⁻¹ J) (h₀⁻¹ * s * h₀) := by
    have h := hJs.conj h₀⁻¹
    rwa [inv_inv] at h
  have e : x = h₀⁻¹ * x * h₀ := by rw [mul_assoc, ← hh₀x, inv_mul_cancel_left]
  have hsx₁ : h₀⁻¹ * s * h₀ * x = x * (h₀⁻¹ * s * h₀) := by
    calc h₀⁻¹ * s * h₀ * x = h₀⁻¹ * s * h₀ * (h₀⁻¹ * x * h₀) := by rw [← e]
      _ = h₀⁻¹ * (s * x) * h₀ := by group
      _ = h₀⁻¹ * (x * s) * h₀ := by rw [hsx]
      _ = (h₀⁻¹ * x * h₀) * (h₀⁻¹ * s * h₀) := by group
      _ = x * (h₀⁻¹ * s * h₀) := by rw [← e]
  have hmz : z = h₀⁻¹ * m * h₀ := by rw [← hm]; group
  have hsne₁ : h₀⁻¹ * s * h₀ ≠ z := by
    intro h
    apply hsne
    calc s = h₀ * (h₀⁻¹ * s * h₀) * h₀⁻¹ := by group
      _ = m := by rw [h, hm]
  have hwJ₁ : h₀⁻¹ * w * h₀ ∈ conjSub h₀⁻¹ J := by
    have h := conj_mem_conjSub (n := h₀⁻¹) hwJ
    rwa [inv_inv] at h
  have hw4₁ : orderOf (h₀⁻¹ * w * h₀) = 4 := by
    rw [← hw4]
    exact (SemiconjBy.orderOf_eq h₀⁻¹ (by unfold SemiconjBy; group)).symm
  have hwz₁ : h₀⁻¹ * w * h₀ * z = z * (h₀⁻¹ * w * h₀) := by
    rw [hmz]
    calc h₀⁻¹ * w * h₀ * (h₀⁻¹ * m * h₀) = h₀⁻¹ * (w * m) * h₀ := by group
      _ = h₀⁻¹ * (m * w) * h₀ := by rw [hwm]
      _ = h₀⁻¹ * m * h₀ * (h₀⁻¹ * w * h₀) := by group
  obtain ⟨h, hh, he⟩ := exists_conj_eq_of_comm hd hx (hΩ.conjInvariant h₀⁻¹ J hJ) hJs₁ hsx₁
    hsne₁ hwJ₁ hw4₁ hwz₁
  refine ⟨h₀ * h, Subgroup.mul_mem _ hh₀ hh, ?_⟩
  calc h₀ * h * z * (h₀ * h)⁻¹ = h₀ * (h * z * h⁻¹) * h₀⁻¹ := by group
    _ = s := by rw [he]; group

theorem exists_comm_of_comm (hd : Sec19DataT p f K z S W L t V) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {s : G} (hJs : IsUniqueInvolution J s)
    (hsne : s ≠ z) {u : G} (huK : u ∈ K) (hu4 : orderOf u = 4) (hus : u * s = s * u) :
    ∃ w ∈ J, orderOf w = 4 ∧ w * z = z * w := by
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hp := hd.tight.branch.odd
  have hq := hd.tight.branch.five
  have hI := isUniqueInvolution_of_tight htb
  have hK := CoreAssembly.mem_conjClass_self K
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_orderOf_four hu4
  obtain ⟨V₀, hV₀, huV₀⟩ := IsSylow2In.exists_ge hu2
    (Subgroup.zpowers_le.mpr ⟨huK, Subgroup.mem_centralizer_singleton_iff.mpr hus⟩ :
      Subgroup.zpowers u ≤ K ⊓ Subgroup.centralizer ({s} : Set G))
  have h4 : 4 ≤ Nat.card V₀ := by
    calc 4 = Nat.card (Subgroup.zpowers u) := by rw [Nat.card_zpowers, hu4]
      _ ≤ Nat.card V₀ := Subgroup.card_le_of_le huV₀
  have hzV₀ : z ∈ V₀ := S1911.mem_of_le_member hI (hV₀.1.trans inf_le_left) hV₀.2.1 (by omega)
  have htwin : K ∉ twinSet (CoreAssembly.conjClass K) J := by
    rintro ⟨-, v, hv₁, hv₂⟩
    have e1 := (hJs.unique v hv₁.mem hv₁.sq).resolve_left hv₁.ne_one
    have e2 := (hI.unique v hv₂.mem hv₂.sq).resolve_left hv₂.ne_one
    exact hsne (e1.symm.trans e2)
  have hKJ : K ≠ J := by
    intro h
    apply hsne
    rw [← h] at hJs
    exact (hI.unique s hJs.mem hJs.sq).resolve_left hJs.ne_one
  rcases l6_2 p f hp hq G _ hΩ J hJ s hJs K hK htwin z hI V₀ hV₀ hzV₀ with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, hVN, -⟩ | ⟨hV4, -⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one] at h4
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hI.sq) hI.ne_one] at h4
    omega
  · have hstar : K ∈ omegaStarNbr (CoreAssembly.conjClass K) J :=
      ⟨hK, hKJ, V₀, hV3, hV₀.1.trans inf_le_left, hVN⟩
    obtain ⟨-, -, U₁, hU₁, hU₁J, hU₁N⟩ := T3.omegaStarNbr_symm (l6_2 p f) hp hq hΩ hJ hK hstar
    have hU₁z : U₁ ≤ Subgroup.centralizer ({z} : Set G) :=
      hU₁N.trans (S1911.normalizer_le_centralizer_member hI)
    obtain ⟨R, -, J₂, -, hRJ₂, hU₁R, hcyc, -, h4'⟩ := hΩ.exists_data_of_mem_USet hp hU₁
    obtain ⟨w, hwU, hww⟩ :=
      exists_mul_self_eq_of_isCyclic hJs hU₁J hcyc (hRJ₂.2.1.to_le hU₁R) h4'
    refine ⟨w, hU₁J hwU, ?_, Subgroup.mem_centralizer_singleton_iff.mp (hU₁z hwU)⟩
    have h1 : ¬ w ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, hww]
      exact hJs.ne_one
    have h2 : w ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two w, hww, pow_two s, hJs.sq]
    rw [orderOf_eq_prime_pow h1 h2]
    norm_num
  · exact absurd ((hV₀.1.trans inf_le_right).trans
      (S1911.centralizer_le_normalizer_member htb hJ hJs))
      (S1911.not_le_normalizer_of_mem_rSet hd.tight.edgeless hK hJ hKJ hV4
        (hV₀.1.trans inf_le_left))

theorem exists_conj_eq_of_comm_u (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {g : G} (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹))
    (hsne : g * z * g⁻¹ ≠ z) {u : G} (huK : u ∈ K) (hu4 : orderOf u = 4)
    (hus : u * (g * z * g⁻¹) = g * z * g⁻¹ * u) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  obtain ⟨w, hwJ, hw4, hwz⟩ := exists_comm_of_comm hd hJ (hI.conj g) hsne huK hu4 hus
  exact exists_conj_eq_of_comm hd hx hJ (hI.conj g) hsx hsne hwJ hw4 hwz

theorem exists_conj_eq_of_comm_t (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {g : G} (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹))
    (hsz : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) (hst : g * z * g⁻¹ * t = t * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hI := isUniqueInvolution_of_tight htb
  have hcomm := S1911.comm_of_mem hd0
  have htW := S1911.mem_W hd
  have hzW : z ∈ W := (S1916.isUniqueInvolution_W_inf hd).mem.1
  by_cases hsz' : g * z * g⁻¹ = z
  · exact ⟨1, Subgroup.one_mem _, by rw [hsz']; group⟩
  by_cases hst' : g * z * g⁻¹ = t
  · rw [hst']
    exact exists_conj_eq_t hd hx
  by_cases hstz : g * z * g⁻¹ = t * z
  · rw [hstz]
    exact exists_conj_eq_mul_z hd hx
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  have hJs := hI.conj g
  by_cases hw : ∃ w ∈ conjSub g K, orderOf w = 4 ∧ w * z = z * w
  · obtain ⟨w, hwJ, hw4, hwz⟩ := hw
    exact exists_conj_eq_of_comm hd hx hJ hJs hsx hsz' hwJ hw4 hwz
  obtain ⟨_, hJc⟩ := hΩ.classical _ hJ
  obtain ⟨e₁⟩ := hJc.nonempty_equiv
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    S1911.centralizer_le_normalizer_member htb hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm)
  have htN : t ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    S1911.centralizer_le_normalizer_member htb hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hst.symm)
  have hzt : z * t = t * z := hcomm z hzW t htW
  rcases exists_orderOf_four_of_four_group (conjSub g K) hd.tight.branch.odd hd.tight.branch.five
      e₁ ⟨z, hzN⟩ ⟨t, htN⟩ hI.sq hd.invL.sq hzt hw with ⟨w, hwJ, hw4, hwt⟩ | ⟨w, hwJ, hw4, hwzt⟩
  · obtain ⟨h₀, hh₀, he⟩ := exists_conj_eq_t hd hx
    exact exists_conj_eq_of_comm' hd hx hJ hJs hsx hh₀ he hst' hwJ hw4 hwt
  · obtain ⟨h₀, hh₀, he⟩ := exists_conj_eq_mul_z hd hx
    have hwm : w * (t * z) = t * z * w := by
      rw [← hzt]
      exact hwzt
    exact exists_conj_eq_of_comm' hd hx hJ hJs hsx hh₀ he hstz hwJ hw4 hwm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
