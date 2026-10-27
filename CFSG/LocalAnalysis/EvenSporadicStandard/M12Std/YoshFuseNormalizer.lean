module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

section Conjugate

variable {G : Type*} [Group G]

def conjSubgroup (g : G) (H : Subgroup G) : Subgroup G where
  carrier := {y | g⁻¹ * y * g ∈ H}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have h := H.mul_mem ha hb
    simpa [mul_assoc] using h
  inv_mem' {a} ha := by
    have h := H.inv_mem ha
    simpa [mul_assoc] using h

@[simp] theorem mem_conjSubgroup {g : G} {H : Subgroup G} {y : G} :
    y ∈ conjSubgroup g H ↔ g⁻¹ * y * g ∈ H := Iff.rfl

theorem mul_mul_inv_mem_conjSubgroup {g : G} {H : Subgroup G} {y : G} (hy : y ∈ H) :
    g * y * g⁻¹ ∈ conjSubgroup g H := by
  simpa [mul_assoc] using hy

theorem card_conjSubgroup (g : G) (H : Subgroup G) :
    Nat.card (conjSubgroup g H) = Nat.card H :=
  Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y * g, y.2⟩
      invFun := fun h => ⟨g * h * g⁻¹, mul_mul_inv_mem_conjSubgroup h.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }

theorem conjSubgroup_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjSubgroup g H ≤ conjSubgroup g K :=
  fun _ hy => h hy

end Conjugate

section SqComm

variable {G : Type*} [Group G]

structure SqCommIn (c : G) (H : Subgroup G) : Prop where
  sq : ∀ y ∈ H, y * y = 1 ∨ y * y = c
  comm : ∀ y ∈ H, ∀ z ∈ H, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c

theorem SqCommIn.mono {c : G} {H K : Subgroup G} (h : SqCommIn c K) (hHK : H ≤ K) :
    SqCommIn c H :=
  ⟨fun y hy => h.sq y (hHK hy), fun y hy z hz => h.comm y (hHK hy) z (hHK hz)⟩

theorem SqCommIn.conj {c k : G} {H : Subgroup G} (h : SqCommIn c H) (hk : k * c = c * k) :
    SqCommIn c (conjSubgroup k H) := by
  have hkc : k * c * k⁻¹ = c := by rw [hk]; simp
  refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
  · have hy' : y * y = k * ((k⁻¹ * y * k) * (k⁻¹ * y * k)) * k⁻¹ := by group
    rcases h.sq _ hy with h1 | h1
    · left; rw [hy', h1]; simp
    · right; rw [hy', h1, hkc]
  · have hyz : ⁅y, z⁆ = k * ⁅k⁻¹ * y * k, k⁻¹ * z * k⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rcases h.comm _ hy _ hz with h1 | h1
    · left; rw [hyz, h1]; simp
    · right; rw [hyz, h1, hkc]

theorem SqCommIn.isPGroup_two {c : G} {H : Subgroup G} (h : SqCommIn c H) (hcc : c * c = 1) :
    IsPGroup 2 H := by
  intro y
  refine ⟨2, Subtype.ext ?_⟩
  have h4 : (y : G) ^ 2 ^ 2 = (y * y) * (y * y) := by
    simp [pow_succ, mul_assoc]
  rw [Subgroup.coe_pow, h4]
  rcases h.sq y y.2 with h1 | h1
  · simp [h1]
  · simp [h1, hcc]

theorem SqCommIn.le_normalizer {c : G} {H A : Subgroup G} (h : SqCommIn c H) (hAH : A ≤ H)
    (hcA : c ∈ A) : H ≤ Subgroup.normalizer (A : Set G) := by
  have key : ∀ y ∈ H, ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro y hy a ha
    have h1 : y * a * y⁻¹ = ⁅y, a⁆ * a := by
      simp only [commutatorElement_def]; group
    rw [h1]
    refine A.mul_mem ?_ ha
    rcases h.comm y hy a (hAH ha) with h2 | h2
    · rw [h2]; exact A.one_mem
    · rw [h2]; exact hcA
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key y hy a, fun ha => ?_⟩
  have h3 := key y⁻¹ (H.inv_mem hy) _ ha
  simpa [mul_assoc] using h3

theorem mem_normalizer_of_unique {c b : G} {E S : Subgroup G} (hE : SqCommIn c E)
    (hbc : b⁻¹ * c = c * b⁻¹) (hbS : ∀ u ∈ E, b⁻¹ * u * b ∈ S)
    (hUE : ∀ D : Subgroup G, D ≤ S → Nat.card D = Nat.card E →
      (∀ y ∈ D, y * y = 1 ∨ y * y = c) → (∀ y ∈ D, ∀ z ∈ D, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c) → D = E) :
    b ∈ Subgroup.normalizer (E : Set G) := by
  have hD : conjSubgroup b⁻¹ E = E := by
    have hconj := hE.conj hbc
    refine hUE _ (fun y hy => ?_) (card_conjSubgroup _ _) hconj.sq hconj.comm
    rw [mem_conjSubgroup] at hy
    simpa [mul_assoc] using hbS _ hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : y ∈ conjSubgroup b⁻¹ E ↔ y ∈ E := by rw [hD]
  rw [mem_conjSubgroup] at h1
  simpa using h1.symm

end SqComm

section SylowTwo

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_ge (K Q : Subgroup G) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ P : Subgroup G, P ≤ K ∧ Q ≤ P ∧ Nat.card P = 2 ^ (Nat.card K).factorization 2 := by
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(P : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, fun y hy => ?_, ?_⟩
  · exact ⟨⟨y, hQK hy⟩, hP hy, rfl⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact P.card_eq_multiplicity

open scoped Pointwise in
theorem exists_conj_le_sylow (K S Q : Subgroup G) (hSK : S ≤ K)
    (hS : Nat.card S = 2 ^ (Nat.card K).factorization 2) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) :
    ∃ k ∈ K, Q ≤ conjSubgroup k S := by
  have hcard : Nat.card (S.subgroupOf K) = 2 ^ (Nat.card K).factorization 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv).trans hS
  obtain ⟨PS, hPS⟩ : ∃ P : Sylow 2 K, (P : Subgroup K) = S.subgroupOf K :=
    ⟨Sylow.ofCard (S.subgroupOf K) hcard, Sylow.coe_ofCard _ _⟩
  obtain ⟨PQ, hPQ⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  haveI : Finite (Sylow 2 K) := Sylow.finite_of_finiteIndex PS
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K PS PQ
  refine ⟨k, k.2, fun y hy => ?_⟩
  have h1 : (⟨y, hQK hy⟩ : K) ∈ (PQ : Subgroup K) := hPQ hy
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, hsy⟩ := h1
  rw [hPS] at hs
  have hsy' : (k : G) * s * (k : G)⁻¹ = y := by
    have := congrArg Subtype.val hsy
    simpa [MulAut.smul_def] using this
  have hks : (k : G)⁻¹ * y * k = s := by
    rw [← hsy']
    simp [mul_assoc]
  rw [mem_conjSubgroup, hks]
  exact hs

end SylowTwo

theorem fuse_into_normalizer {G : Type*} [Group G] [Finite G]
    (c e x : G) (E S R T Tx : Subgroup G)
    (hc1 : c ≠ 1) (hcE : c ∈ E) (hES : E ≤ S)
    (hSC : ∀ s ∈ S, s * c = c * s)
    (hSyl : Nat.card S = 2 ^ (Nat.card (Subgroup.centralizer ({c} : Set G))).factorization 2)
    (hEsq : ∀ y ∈ E, y * y = 1 ∨ y * y = c)
    (hEcomm : ∀ y ∈ E, ∀ z ∈ E, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c)
    (hUE : ∀ D : Subgroup G, D ≤ S → Nat.card D = Nat.card E →
      (∀ y ∈ D, y * y = 1 ∨ y * y = c) → (∀ y ∈ D, ∀ z ∈ D, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c) → D = E)
    (heE : e ∈ E) (hec : e * c = c * e)
    (hRdef : R = E ⊓ Subgroup.centralizer ({e} : Set G))
    (hRT : R ≤ T) (hTe : ∀ y ∈ T, y * e = e * y)
    (hTSyl : Nat.card T = 2 ^ (Nat.card (Subgroup.centralizer ({e} : Set G))).factorization 2)
    (hTR : Nat.card T = 2 * Nat.card R)
    (hZT : ∀ y ∈ T, (∀ z ∈ T, y * z = z * y) → y = 1 ∨ y = e ∨ y = c ∨ y = e * c)
    (hZR : ∀ y ∈ R, (∀ z ∈ R, y * z = z * y) → y = 1 ∨ y = e ∨ y = c ∨ y = e * c)
    (hRuniq : ∀ D : Subgroup G, D ≤ T → Nat.card D = Nat.card R →
      (∀ y ∈ D, y * y = 1 ∨ y * y = c) → (∀ y ∈ D, ∀ z ∈ D, ⁅y, z⁆ = 1 ∨ ⁅y, z⁆ = c) → D = R)
    (hnsq : ¬ ∃ z : G, z * z = e) (hcsq : ∃ z : G, z * z = c)
    (hswap : ∃ d : G, d * e * d⁻¹ = e * c)
    (hxE : x ∈ E) (hxc : x ≠ c)
    (hconj : ∃ g : G, g * x * g⁻¹ = e)
    (hTx : ∀ y ∈ Tx, y * x = x * y) (hTxc : ∀ y ∈ Tx, y * c = c * y)
    (hTxcard : Nat.card Tx = Nat.card T)
    (hRx : ∀ y ∈ E, y * x = x * y → y ∈ Tx)
    (hRxcard : Nat.card (E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = Nat.card R) :
    ∃ ℓ ∈ Subgroup.normalizer (E : Set G), ℓ * x * ℓ⁻¹ = e ∨ ℓ * x * ℓ⁻¹ = e * c := by
  have hcc : c * c = 1 := by
    rcases hEsq c hcE with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one c).symm)) hc1
  obtain ⟨C, hCmem, hSyl⟩ : ∃ C : Subgroup G, (∀ y, y ∈ C ↔ y * c = c * y) ∧
      Nat.card S = 2 ^ (Nat.card C).factorization 2 :=
    ⟨Subgroup.centralizer ({c} : Set G), fun y => Subgroup.mem_centralizer_singleton_iff, hSyl⟩
  have hSle : S ≤ C := fun s hs => (hCmem s).2 (hSC s hs)
  have hEC : E ≤ C := hES.trans hSle
  have hE : SqCommIn c E := ⟨hEsq, hEcomm⟩
  obtain ⟨g, hgx, hgTx⟩ : ∃ g : G, g * x * g⁻¹ = e ∧ conjSubgroup g Tx = T := by
    obtain ⟨g₀, hg₀⟩ := hconj
    have hTK : T ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (hTe y hy)
    have hQK : conjSubgroup g₀ Tx ≤ Subgroup.centralizer ({e} : Set G) := by
      intro y hy
      rw [mem_conjSubgroup] at hy
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg₀]
      have h1 := hTx _ hy
      calc y * (g₀ * x * g₀⁻¹) = g₀ * ((g₀⁻¹ * y * g₀) * x) * g₀⁻¹ := by group
        _ = g₀ * (x * (g₀⁻¹ * y * g₀)) * g₀⁻¹ := by rw [h1]
        _ = g₀ * x * g₀⁻¹ * y := by group
    have hQ : IsPGroup 2 (conjSubgroup g₀ Tx) :=
      IsPGroup.of_card (by rw [card_conjSubgroup, hTxcard, hTSyl])
    obtain ⟨k, hkK, hk⟩ := exists_conj_le_sylow _ T _ hTK hTSyl hQK hQ
    have hke : k * e = e * k := Subgroup.mem_centralizer_singleton_iff.1 hkK
    refine ⟨k⁻¹ * g₀, ?_, ?_⟩
    · calc k⁻¹ * g₀ * x * (k⁻¹ * g₀)⁻¹ = k⁻¹ * (g₀ * x * g₀⁻¹) * k := by group
        _ = e := by rw [hg₀, mul_assoc, ← hke, inv_mul_cancel_left]
    · refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_)
        (le_of_eq (by rw [card_conjSubgroup, hTxcard]))
      rw [mem_conjSubgroup] at hy
      have h1 : k * y * k⁻¹ ∈ conjSubgroup g₀ Tx := by
        rw [mem_conjSubgroup]
        convert hy using 1
        group
      have h2 := mem_conjSubgroup.1 (hk h1)
      simpa [mul_assoc] using h2
  have hcTx : c ∈ Tx := hRx c hcE (hSC x (hES hxE)).symm
  have hzT : g * c * g⁻¹ ∈ T := hgTx ▸ mul_mul_inv_mem_conjSubgroup hcTx
  have hzcent : ∀ t ∈ T, g * c * g⁻¹ * t = t * (g * c * g⁻¹) := by
    intro t ht
    rw [← hgTx, mem_conjSubgroup] at ht
    have h1 := hTxc _ ht
    calc g * c * g⁻¹ * t = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by rw [h1]
      _ = t * (g * c * g⁻¹) := by group
  have hgc : g * c * g⁻¹ = c := by
    rcases hZT _ hzT hzcent with h | h | h | h
    · exact absurd (by simpa using h) hc1
    · exact absurd (by simpa using h.trans hgx.symm) hxc.symm
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := hcsq
      obtain ⟨d, hd⟩ := hswap
      refine hnsq ⟨d⁻¹ * (g * w * g⁻¹) * d, ?_⟩
      calc d⁻¹ * (g * w * g⁻¹) * d * (d⁻¹ * (g * w * g⁻¹) * d)
          = d⁻¹ * (g * (w * w) * g⁻¹) * d := by group
        _ = d⁻¹ * (g * c * g⁻¹) * d := by rw [hw]
        _ = d⁻¹ * (e * c) * d := by rw [h]
        _ = d⁻¹ * (d * e * d⁻¹) * d := by rw [hd]
        _ = e := by group
  have hgC : g * c = c * g := by
    calc g * c = (g * c * g⁻¹) * g := by group
      _ = c * g := by rw [hgc]
  have hR'R : conjSubgroup g (E ⊓ Subgroup.centralizer ({x} : Set G)) = R := by
    have hsc : SqCommIn c (conjSubgroup g (E ⊓ Subgroup.centralizer ({x} : Set G))) :=
      (hE.mono inf_le_left).conj hgC
    refine hRuniq _ (fun y hy => ?_) ((card_conjSubgroup _ _).trans hRxcard) hsc.sq hsc.comm
    rw [mem_conjSubgroup, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [← hgTx, mem_conjSubgroup]
    exact hRx _ hy.1 hy.2
  have hcR : c ∈ R := by
    rw [hRdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨hcE, hec.symm⟩
  have heR : e ∈ R := by
    rw [hRdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨heE, rfl⟩
  have hRe : ∀ r ∈ R, r * e = e * r := fun r hr => by
    rw [hRdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hr
    exact hr.2
  have hRE : R ≤ E := by rw [hRdef]; exact inf_le_left
  have hE' : SqCommIn c (conjSubgroup g E) := hE.conj hgC
  have hRE' : R ≤ conjSubgroup g E := by
    rw [← hR'R]; exact conjSubgroup_mono g inf_le_left
  have hEN : E ≤ Subgroup.normalizer (R : Set G) := hE.le_normalizer hRE hcR
  have hE'N : conjSubgroup g E ≤ Subgroup.normalizer (R : Set G) :=
    hE'.le_normalizer hRE' hcR
  have hE'C : conjSubgroup g E ≤ C := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h1 := (hCmem _).1 (hEC hy)
    rw [hCmem]
    calc y * c = y * (g * c * g⁻¹) := by rw [hgc]
      _ = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * y := by group
      _ = c * y := by rw [hgc]
  obtain ⟨P, hPK, hEP, hPcard⟩ := exists_sylow_ge _ E (le_inf hEN hEC) (hE.isPGroup_two hcc)
  obtain ⟨m, hmK, hm⟩ := exists_conj_le_sylow _ P (conjSubgroup g E) hPK hPcard
    (le_inf hE'N hE'C) (hE'.isPGroup_two hcc)
  obtain ⟨k, hkC, hk⟩ := exists_conj_le_sylow C S P hSle hSyl (hPK.trans inf_le_right)
    (IsPGroup.of_card hPcard)
  obtain ⟨hmN, hmC⟩ := Subgroup.mem_inf.1 hmK
  have hkc : k * c = c * k := (hCmem k).1 hkC
  have hmc : m * c = c * m := (hCmem m).1 hmC
  have hkn : k ∈ Subgroup.normalizer (E : Set G) :=
    mem_normalizer_of_unique hE (Commute.inv_left (show Commute k c from hkc))
      (fun u hu => mem_conjSubgroup.1 (hk (hEP hu))) hUE
  have hbn : g⁻¹ * (m * k) ∈ Subgroup.normalizer (E : Set G) := by
    have hbc : Commute (g⁻¹ * (m * k)) c :=
      (Commute.inv_left (show Commute g c from hgC)).mul_left
        ((show Commute m c from hmc).mul_left (show Commute k c from hkc))
    refine mem_normalizer_of_unique hE hbc.inv_left (fun u hu => ?_) hUE
    have h1 : m⁻¹ * (g * u * g⁻¹) * m ∈ P :=
      mem_conjSubgroup.1 (hm (mul_mul_inv_mem_conjSubgroup hu))
    have h2 : k⁻¹ * (m⁻¹ * (g * u * g⁻¹) * m) * k ∈ S := mem_conjSubgroup.1 (hk h1)
    convert h2 using 1
    group
  have hℓ : m⁻¹ * g ∈ Subgroup.normalizer (E : Set G) := by
    have h1 : m⁻¹ * g = k * (g⁻¹ * (m * k))⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ hkn (Subgroup.inv_mem _ hbn)
  have hmR : ∀ z, z ∈ R ↔ m * z * m⁻¹ ∈ R := Subgroup.mem_normalizer_iff.1 hmN
  have hm'R : ∀ z, z ∈ R ↔ m⁻¹ * z * m ∈ R := by
    intro z
    simpa using Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hmN) z
  have hmeR : m⁻¹ * e * m ∈ R := (hm'R e).1 heR
  have hcent : ∀ z ∈ R, m⁻¹ * e * m * z = z * (m⁻¹ * e * m) := by
    intro z hz
    have her := hRe _ ((hmR z).1 hz)
    calc m⁻¹ * e * m * z = m⁻¹ * (e * (m * z * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * z * m⁻¹) * e) * m := by rw [her]
      _ = z * (m⁻¹ * e * m) := by group
  refine ⟨m⁻¹ * g, hℓ, ?_⟩
  have hℓx : m⁻¹ * g * x * (m⁻¹ * g)⁻¹ = m⁻¹ * e * m := by
    rw [← hgx]; group
  rw [hℓx]
  rcases hZR _ hmeR hcent with h | h | h | h
  · exfalso
    refine hnsq ⟨1, ?_⟩
    calc (1 : G) * 1 = m * (m⁻¹ * e * m) * m⁻¹ := by rw [h]; group
      _ = e := by group
  · exact Or.inl h
  · exfalso
    obtain ⟨w, hw⟩ := hcsq
    refine hnsq ⟨m * w * m⁻¹, ?_⟩
    calc m * w * m⁻¹ * (m * w * m⁻¹) = m * (w * w) * m⁻¹ := by group
      _ = m * c * m⁻¹ := by rw [hw]
      _ = m * (m⁻¹ * e * m) * m⁻¹ := by rw [h]
      _ = e := by group
  · exact Or.inr h

end CFSG.EvenSporadicStandard.M12Std.Yosh
