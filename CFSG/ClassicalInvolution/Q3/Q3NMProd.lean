module

public import CFSG.ClassicalInvolution.Q3.Q3NMLie
public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Join

variable {G : Type} [Group G] {ι : Type} [DecidableEq ι] {S : ι → Subgroup G}

omit [DecidableEq ι] in
theorem mul_comm_of_mem_iSup
    (hc : ∀ i j, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a) {j : ι} {s : Finset ι}
    (hj : j ∉ s) {a b : G} (ha : a ∈ S j) (hb : b ∈ ⨆ i ∈ s, S i) : a * b = b * a := by
  have hle : (⨆ i ∈ s, S i) ≤ Subgroup.centralizer (S j : Set G) := by
    refine iSup₂_le fun i hi => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hc j i (fun h => hj (h ▸ hi)) y hy x hx
  exact Subgroup.mem_centralizer_iff.mp (hle hb) a ha

omit [DecidableEq ι] in
theorem eq_of_mul_eq_mul_of_inf_eq_bot {j : ι} {s : Finset ι}
    (hint : S j ⊓ (⨆ i ∈ s, S i) = ⊥) {a a' b b' : G} (ha : a ∈ S j) (ha' : a' ∈ S j)
    (hb : b ∈ ⨆ i ∈ s, S i) (hb' : b' ∈ ⨆ i ∈ s, S i) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ S j ⊓ (⨆ i ∈ s, S i) := by
    refine ⟨(S j).mul_mem ((S j).inv_mem ha') ha, ?_⟩
    rw [h1]
    exact (⨆ i ∈ s, S i).mul_mem hb' ((⨆ i ∈ s, S i).inv_mem hb)
  rw [hint, Subgroup.mem_bot] at h2
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨e1, ?_⟩
  subst e1
  exact mul_left_cancel h

theorem exists_mul_of_mem_insert
    (hc : ∀ i j, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a) {j : ι} {s : Finset ι}
    (hj : j ∉ s) {x : G} (hx : x ∈ ⨆ i ∈ insert j s, S i) :
    ∃ a ∈ S j, ∃ b ∈ ⨆ i ∈ s, S i, a * b = x := by
  rw [Finset.iSup_insert] at hx
  exact (mem_sup_iff_of_commute (fun a ha b hb => mul_comm_of_mem_iSup hc hj ha hb)).mp hx

end Join

section Comm

variable {G : Type} [Group G] [Finite G]

theorem comm_of_oddCoreIn_eq_bot {C B : Subgroup G} (hBC : B ≤ C) (hB : oddCoreIn B = ⊥) {n : G}
    (hn : n ∈ oddCoreIn C) (hnorm : ∀ r ∈ B, n * r * n⁻¹ ∈ B) : ∀ r ∈ B, n * r = r * n := by
  intro r hr
  have hrC : r ∈ C := hBC hr
  have hcN : n * r * n⁻¹ * r⁻¹ ∈ oddCoreIn C := by
    have h1 : r * n⁻¹ * r⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn hrC ((oddCoreIn C).inv_mem hn)
    have : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
    rw [this]
    exact (oddCoreIn C).mul_mem hn h1
  have hcX : n * r * n⁻¹ * r⁻¹ ∈ B := B.mul_mem (hnorm r hr) (B.inv_mem hr)
  have hS : oddCoreIn C ⊓ B ≤ oddCoreIn B := by
    refine le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
    · intro u hu
      have huC : u ∈ C := hBC hu
      have huC' : u⁻¹ ∈ C := C.inv_mem huC
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨conj_mem_oddCoreIn huC hy1, B.mul_mem (B.mul_mem hu hy2) (B.inv_mem hu)⟩
      · rintro ⟨hy1, hy2⟩
        have h1 := conj_mem_oddCoreIn huC' hy1
        have h2 := B.mul_mem (B.mul_mem (B.inv_mem hu) hy2) hu
        simp only [inv_inv, mul_assoc, inv_mul_cancel_left] at h1 h2 ⊢
        exact ⟨by simpa [mul_assoc] using h1, by simpa [mul_assoc] using h2⟩
    · exact (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : n * r * n⁻¹ * r⁻¹ ∈ oddCoreIn B := hS ⟨hcN, hcX⟩
  rw [hB, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Comm

section Data

variable {G : Type} [Group G] {ι : Type}

structure PermProd (S : ι → Subgroup G) (σ : MulAut G) (π : ι → ι) : Prop where
  comm : ∀ i j, i ≠ j → ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a
  indep : ∀ (j : ι) (s : Finset ι), j ∉ s → S j ⊓ (⨆ i ∈ s, S i) = ⊥
  gen : ⨆ i, S i = ⊤
  sq : σ * σ = 1
  invol : Function.Involutive π
  map : ∀ i, (S i).map (σ : G →* G) = S (π i)

variable {S : ι → Subgroup G} {σ : MulAut G} {π : ι → ι}

theorem PermProd.conj_mem (h : PermProd S σ π) (i : ι) (g : G) {x : G} (hx : x ∈ S i) :
    g * x * g⁻¹ ∈ S i := by
  have hg : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
  rw [← h.gen] at hg
  have hle : (⨆ l, S l) ≤ Subgroup.normalizer (S i : Set G) := by
    refine iSup_le fun l => ?_
    by_cases hli : l = i
    · subst hli
      exact Subgroup.le_normalizer
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      have fwd : ∀ g ∈ S l, ∀ y ∈ S i, g * y * g⁻¹ ∈ S i := by
        intro g hg y hy
        rw [h.comm l i hli g hg y hy]
        simpa using hy
      intro y
      exact ⟨fun hy => fwd g hg y hy, fun hy => by
        simpa [mul_assoc] using fwd g⁻¹ ((S l).inv_mem hg) _ hy⟩
  exact (Subgroup.mem_normalizer_iff.mp (hle hg) x).mp hx

theorem PermProd.apply_mem (h : PermProd S σ π) {i : ι} {x : G} (hx : x ∈ S i) :
    σ x ∈ S (π i) := by
  have : σ x ∈ (S i).map (σ : G →* G) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [h.map i] at this

theorem PermProd.apply_apply (h : PermProd S σ π) (x : G) : σ (σ x) = x :=
  apply_apply_of_mul_eq_one h.sq x

theorem PermProd.apply_mem_iSup (h : PermProd S σ π) {s : Finset ι} (hs : ∀ i ∈ s, π i ∈ s)
    {x : G} (hx : x ∈ ⨆ i ∈ s, S i) : σ x ∈ ⨆ i ∈ s, S i := by
  have hle : (⨆ i ∈ s, S i) ≤ (⨆ i ∈ s, S i).comap (σ : G →* G) := by
    refine iSup₂_le fun i hi => ?_
    intro y hy
    show σ y ∈ ⨆ i ∈ s, S i
    exact Subgroup.mem_iSup_of_mem (π i) (Subgroup.mem_iSup_of_mem (hs i hi) (h.apply_mem hy))
  exact hle hx

theorem mem_iSup_of_mem_finset {s : Finset ι} {i : ι} (hi : i ∈ s) {x : G} (hx : x ∈ S i) :
    x ∈ ⨆ i ∈ s, S i :=
  Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi hx)

theorem iSup_finset_mono {s t : Finset ι} (hst : s ⊆ t) {x : G} (hx : x ∈ ⨆ i ∈ s, S i) :
    x ∈ ⨆ i ∈ t, S i := by
  have h1 : (⨆ i ∈ s, S i) ≤ ⨆ i ∈ t, S i := biSup_mono (fun i hi => hst hi)
  exact h1 hx

theorem mem_iSup_singleton {j : ι} {x : G} : x ∈ ⨆ i ∈ ({j} : Finset ι), S i ↔ x ∈ S j := by
  simp

end Data

section Decomp

variable {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Subgroup G} {σ : MulAut G} {π : ι → ι}

theorem PermProd.erase_stable (h : PermProd S σ π) {k : ι} (hk : π k = k) :
    ∀ i ∈ Finset.univ.erase k, π i ∈ Finset.univ.erase k := by
  intro i hi
  rw [Finset.mem_erase] at hi ⊢
  refine ⟨fun hpi => hi.1 ?_, Finset.mem_univ _⟩
  have := h.invol i
  rw [hpi, hk] at this
  exact this.symm

theorem PermProd.top_decomp (h : PermProd S σ π) (k : ι) {n : G} :
    n ∈ ⨆ i ∈ insert k (Finset.univ.erase k), S i := by
  rw [Finset.insert_erase (Finset.mem_univ k)]
  simp only [Finset.mem_univ, iSup_pos]
  rw [h.gen]
  exact Subgroup.mem_top n

theorem PermProd.fixed_decomp (h : PermProd S σ π) {k : ι} (hk : π k = k) {n : G}
    (hn : σ n = n) :
    ∃ a ∈ S k, ∃ b ∈ ⨆ i ∈ Finset.univ.erase k, S i, a * b = n ∧ σ a = a ∧ σ b = b := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_insert h.comm (Finset.notMem_erase k _) (h.top_decomp k (n := n))
  have hσa : σ a ∈ S k := by simpa [hk] using h.apply_mem ha
  have hσb : σ b ∈ ⨆ i ∈ Finset.univ.erase k, S i := h.apply_mem_iSup (h.erase_stable hk) hb
  have hσab : σ a * σ b = a * b := by
    rw [← map_mul, hab]
    exact hn
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.indep k _ (Finset.notMem_erase k _))
    hσa ha hσb hb hσab
  exact ⟨a, ha, b, hb, hab, h1, h2⟩

theorem PermProd.swap_decomp (h : PermProd S σ π) {k : ι} (hk : π k ≠ k) {n : G}
    (hn : σ n = n) :
    ∃ a ∈ S k, ∃ b ∈ ⨆ i ∈ (Finset.univ.erase k).erase (π k), S i,
      σ b = b ∧ n = a * (σ a * b) := by
  have hπj : π (π k) = k := h.invol k
  have hjs' : π k ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩
  have hks' : k ∉ Finset.univ.erase k := Finset.notMem_erase k _
  have hjs : π k ∉ (Finset.univ.erase k).erase (π k) := Finset.notMem_erase _ _
  have hstab : ∀ i ∈ (Finset.univ.erase k).erase (π k),
      π i ∈ (Finset.univ.erase k).erase (π k) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_erase] at hi ⊢
    obtain ⟨hij, hik, _⟩ := hi
    refine ⟨?_, ?_, Finset.mem_univ _⟩
    · intro hpi
      apply hik
      have := h.invol i
      rw [hpi, hπj] at this
      exact this.symm
    · intro hpi
      apply hij
      have := h.invol i
      rw [hpi] at this
      exact this.symm
  obtain ⟨a, ha, w, hw, hnaw⟩ :=
    exists_mul_of_mem_insert h.comm hks' (h.top_decomp k (n := n))
  have hw' : w ∈ ⨆ i ∈ insert (π k) ((Finset.univ.erase k).erase (π k)), S i := by
    rw [Finset.insert_erase hjs']
    exact hw
  obtain ⟨c, hc, b, hb, hcb⟩ := exists_mul_of_mem_insert h.comm hjs hw'
  have e : n = a * (c * b) := by rw [hcb, hnaw]
  have hσa : σ a ∈ S (π k) := h.apply_mem ha
  have hσc : σ c ∈ S k := by simpa [hπj] using h.apply_mem hc
  have hσb : σ b ∈ ⨆ i ∈ (Finset.univ.erase k).erase (π k), S i := h.apply_mem_iSup hstab hb
  have hn' : σ a * (σ c * σ b) = a * (c * b) := by
    calc σ a * (σ c * σ b) = σ (a * (c * b)) := by simp only [map_mul]
      _ = σ n := by rw [e]
      _ = a * (c * b) := by rw [hn, e]
  have hcomm : σ a * σ c = σ c * σ a := h.comm (π k) k hk (σ a) hσa (σ c) hσc
  have hn'' : σ c * (σ a * σ b) = a * (c * b) := by
    rw [← mul_assoc, ← hcomm, mul_assoc]
    exact hn'
  have hm1 : σ a * σ b ∈ ⨆ i ∈ Finset.univ.erase k, S i :=
    (⨆ i ∈ Finset.univ.erase k, S i).mul_mem (mem_iSup_of_mem_finset hjs' hσa)
      (iSup_finset_mono (Finset.erase_subset _ _) hσb)
  have hm2 : c * b ∈ ⨆ i ∈ Finset.univ.erase k, S i :=
    (⨆ i ∈ Finset.univ.erase k, S i).mul_mem (mem_iSup_of_mem_finset hjs' hc)
      (iSup_finset_mono (Finset.erase_subset _ _) hb)
  obtain ⟨_, h2⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.indep k _ hks') hσc ha hm1 hm2 hn''
  obtain ⟨h3, h4⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.indep (π k) _ hjs) hσa hc hσb hb h2
  exact ⟨a, ha, b, hb, h4, by rw [h3]; exact e⟩

end Decomp

section Key

variable {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Subgroup G} {σ : MulAut G} {π : ι → ι}

theorem PermProd.mem_erase_of_fixed (h : PermProd S σ π)
    (hfix : ∀ i, π i = i → oddCoreIn (S i ⊓ fixedSubgroup σ) = ⊥) {n : G}
    (hn : n ∈ oddCoreIn (fixedSubgroup σ)) {k : ι} (hk : π k = k) :
    n ∈ ⨆ i ∈ Finset.univ.erase k, S i := by
  have hnC : n ∈ fixedSubgroup σ := oddCoreIn_le _ hn
  have hσn : σ n = n := hnC
  have hm : Odd (orderOf n) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hn)
  obtain ⟨a, ha, b, hb, hab, haσ, hbσ⟩ := h.fixed_decomp hk hσn
  have hks : k ∉ Finset.univ.erase k := Finset.notMem_erase k _
  have haB : a ∈ S k ⊓ fixedSubgroup σ := ⟨ha, haσ⟩
  have hcommB : ∀ u ∈ S k ⊓ fixedSubgroup σ, n * u = u * n := by
    refine comm_of_oddCoreIn_eq_bot inf_le_right (hfix k hk) hn ?_
    intro r hr
    exact ⟨h.conj_mem k n hr.1, (fixedSubgroup σ).mul_mem
      ((fixedSubgroup σ).mul_mem hnC hr.2) ((fixedSubgroup σ).inv_mem hnC)⟩
  have hacomm : ∀ u ∈ S k ⊓ fixedSubgroup σ, a * u = u * a := by
    intro u hu
    have h1 : u * b = b * u := mul_comm_of_mem_iSup h.comm hks hu.1 hb
    have h2 := hcommB u hu
    rw [← hab] at h2
    have h3 : a * u * b = u * a * b := by
      calc a * u * b = a * (u * b) := by group
        _ = a * (b * u) := by rw [h1]
        _ = a * b * u := by group
        _ = u * (a * b) := h2.symm.symm
        _ = u * a * b := by group
    exact mul_right_cancel h3
  have habc : a * b = b * a := mul_comm_of_mem_iSup h.comm hks ha hb
  have ham : a ^ orderOf n = 1 := by
    have h1 : a ^ orderOf n * b ^ orderOf n = 1 * 1 := by
      rw [← Commute.mul_pow habc, hab, mul_one]
      exact pow_orderOf_eq_one n
    exact (eq_of_mul_eq_mul_of_inf_eq_bot (h.indep k _ hks) ((S k).pow_mem ha _)
      (S k).one_mem ((⨆ i ∈ Finset.univ.erase k, S i).pow_mem hb _) (Subgroup.one_mem _) h1).1
  have ha1 : a = 1 := eq_one_of_central_of_oddCoreIn_eq_bot (hfix k hk) haB hacomm hm ham
  rw [← hab, ha1, one_mul]
  exact hb

theorem PermProd.mem_erase_of_swap (h : PermProd S σ π)
    (hswap : ∀ i, π i ≠ i → oddCoreIn (S i) = ⊥) {n : G}
    (hn : n ∈ oddCoreIn (fixedSubgroup σ)) {k : ι} (hk : π k ≠ k) :
    n ∈ ⨆ i ∈ Finset.univ.erase k, S i := by
  have hnC : n ∈ fixedSubgroup σ := oddCoreIn_le _ hn
  have hσn : σ n = n := hnC
  have hm : Odd (orderOf n) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hn)
  obtain ⟨a, ha, b, hb, hbσ, hneq⟩ := h.swap_decomp hk hσn
  have hks' : k ∉ Finset.univ.erase k := Finset.notMem_erase k _
  have hjs' : π k ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩
  have hjs : π k ∉ (Finset.univ.erase k).erase (π k) := Finset.notMem_erase _ _
  have hks : k ∉ (Finset.univ.erase k).erase (π k) := fun hh =>
    hks' (Finset.mem_of_mem_erase hh)
  have hkj : k ≠ π k := Ne.symm hk
  have hσa : σ a ∈ S (π k) := h.apply_mem ha
  have hσk : ∀ u ∈ S k, σ u ∈ S (π k) := fun u hu => h.apply_mem hu
  let Φ : ↥(S k) →* G := MonoidHom.mk' (fun u : ↥(S k) => (u : G) * σ (u : G)) (by
    intro u v
    have hc : (v : G) * σ (u : G) = σ (u : G) * (v : G) := h.comm k (π k) hkj v v.2 _ (hσk u u.2)
    show ((u * v : ↥(S k)) : G) * σ ((u * v : ↥(S k)) : G) = _
    simp only [Subgroup.coe_mul, map_mul]
    calc (u : G) * v * (σ u * σ v) = u * (v * σ u) * σ v := by group
      _ = u * (σ u * v) * σ v := by rw [hc]
      _ = u * σ u * (v * σ v) := by group)
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : (u : G) * σ (u : G) = 1 := hu
    have hu1 : (u : G) ∈ S k ⊓ ⨆ i ∈ ({π k} : Finset ι), S i := by
      refine ⟨u.2, mem_iSup_singleton.mpr ?_⟩
      have : (u : G) = (σ (u : G))⁻¹ := eq_inv_of_mul_eq_one_left hu'
      rw [this]
      exact (S (π k)).inv_mem (hσk u u.2)
    rw [h.indep k {π k} (by simpa using hkj), Subgroup.mem_bot] at hu1
    exact Subtype.ext hu1
  have hSk : oddCoreIn (⊤ : Subgroup ↥(S k)) = ⊥ := by
    have h1 := map_oddCoreIn_subtype (Y := S k) (⊤ : Subgroup ↥(S k))
    rw [Subgroup.map_top, Subgroup.range_subtype, hswap k hk] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (S k).subtype_injective).mp h1
  have hDbot : oddCoreIn ((⊤ : Subgroup ↥(S k)).map Φ) = ⊥ := oddCoreIn_map_eq_bot Φ hΦinj hSk
  have hDC : (⊤ : Subgroup ↥(S k)).map Φ ≤ fixedSubgroup σ := by
    rintro _ ⟨u, -, rfl⟩
    show σ ((u : G) * σ (u : G)) = (u : G) * σ (u : G)
    rw [map_mul, h.apply_apply]
    exact (h.comm k (π k) hkj u u.2 _ (hσk u u.2)).symm
  have hDnorm : ∀ r ∈ (⊤ : Subgroup ↥(S k)).map Φ,
      n * r * n⁻¹ ∈ (⊤ : Subgroup ↥(S k)).map Φ := by
    rintro _ ⟨u, -, rfl⟩
    refine ⟨⟨n * u * n⁻¹, h.conj_mem k n u.2⟩, trivial, ?_⟩
    show n * u * n⁻¹ * σ (n * u * n⁻¹) = n * (u * σ u) * n⁻¹
    rw [map_mul, map_mul, map_inv, hσn]
    group
  have hcommD := comm_of_oddCoreIn_eq_bot hDC hDbot hn hDnorm
  have hacomm : ∀ u ∈ S k, a * u = u * a := by
    intro u hu
    have h4 := hcommD (u * σ u) ⟨⟨u, hu⟩, trivial, rfl⟩
    rw [hneq] at h4
    have hub : u * b = b * u := mul_comm_of_mem_iSup h.comm hks hu hb
    have hσub : σ u * b = b * σ u :=
      mul_comm_of_mem_iSup h.comm hjs (hσk u hu) hb
    have h5 : a * σ a * (u * σ u) * b = u * σ u * (a * σ a) * b := by
      calc a * σ a * (u * σ u) * b = a * σ a * u * (σ u * b) := by group
        _ = a * σ a * u * (b * σ u) := by rw [hσub]
        _ = a * σ a * (u * b) * σ u := by group
        _ = a * σ a * (b * u) * σ u := by rw [hub]
        _ = a * (σ a * b) * (u * σ u) := by group
        _ = u * σ u * (a * (σ a * b)) := h4
        _ = u * σ u * (a * σ a) * b := by group
    have h6 := mul_right_cancel h5
    have hσau : σ a * u = u * σ a := (h.comm k (π k) hkj u hu (σ a) hσa).symm
    have hσua : σ u * a = a * σ u := (h.comm k (π k) hkj a ha (σ u) (hσk u hu)).symm
    have h7 : a * u * (σ a * σ u) = u * a * (σ u * σ a) := by
      calc a * u * (σ a * σ u) = a * (σ a * u) * σ u := by rw [hσau]; group
        _ = a * σ a * (u * σ u) := by group
        _ = u * σ u * (a * σ a) := h6
        _ = u * (σ u * a) * σ a := by group
        _ = u * a * (σ u * σ a) := by rw [hσua]; group
    exact (eq_of_mul_eq_mul_of_inf_eq_bot (h.indep k {π k} (by simpa using hkj))
      ((S k).mul_mem ha hu) ((S k).mul_mem hu ha)
      (mem_iSup_singleton.mpr ((S (π k)).mul_mem hσa (hσk u hu)))
      (mem_iSup_singleton.mpr ((S (π k)).mul_mem (hσk u hu) hσa)) h7).1
  have ham : a ^ orderOf n = 1 := by
    have hcab : Commute a (σ a * b) :=
      Commute.mul_right (h.comm k (π k) hkj a ha (σ a) hσa)
        (mul_comm_of_mem_iSup h.comm hks ha hb)
    have hcσb : Commute (σ a) b := mul_comm_of_mem_iSup h.comm hjs hσa hb
    have h1 : a ^ orderOf n * (σ a ^ orderOf n * b ^ orderOf n) = 1 * 1 := by
      rw [← Commute.mul_pow hcσb, ← Commute.mul_pow hcab, ← hneq, mul_one]
      exact pow_orderOf_eq_one n
    have hmem : σ a ^ orderOf n * b ^ orderOf n ∈ ⨆ i ∈ Finset.univ.erase k, S i :=
      (⨆ i ∈ Finset.univ.erase k, S i).mul_mem
        (Subgroup.pow_mem _ (mem_iSup_of_mem_finset hjs' hσa) _)
        (Subgroup.pow_mem _ (iSup_finset_mono (Finset.erase_subset _ _) hb) _)
    exact (eq_of_mul_eq_mul_of_inf_eq_bot (h.indep k _ hks') ((S k).pow_mem ha _)
      (S k).one_mem hmem (Subgroup.one_mem _) h1).1
  have ha1 : a = 1 := eq_one_of_central_of_oddCoreIn_eq_bot (hswap k hk) ha hacomm hm ham
  rw [hneq, ha1, map_one, one_mul, one_mul]
  exact iSup_finset_mono (Finset.erase_subset _ _) hb

omit [Finite G] in
theorem PermProd.eq_one_of_mem_all_erase (h : PermProd S σ π) {n : G}
    (hall : ∀ k, n ∈ ⨆ i ∈ Finset.univ.erase k, S i) : n = 1 := by
  have hind : ∀ s : Finset ι, n ∈ ⨆ i ∈ Finset.univ \ s, S i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sdiff_empty, Finset.mem_univ, iSup_pos]
      rw [h.gen]
      exact Subgroup.mem_top n
    | insert j s hj ih =>
      have hj' : j ∉ Finset.univ \ insert j s := by simp
      have hins : insert j (Finset.univ \ insert j s) = Finset.univ \ s := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hxj : x = j
        · subst hxj
          simp [hj]
        · simp [hxj]
      rw [← hins] at ih
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_insert h.comm hj' ih
      have hbj : b ∈ ⨆ i ∈ Finset.univ.erase j, S i :=
        iSup_finset_mono (fun x hx => Finset.mem_erase.mpr
          ⟨fun hxj => (Finset.mem_sdiff.mp hx).2 (hxj ▸ Finset.mem_insert_self j s),
            Finset.mem_univ x⟩) hb
      have han : a ∈ ⨆ i ∈ Finset.univ.erase j, S i := by
        have : a = n * b⁻¹ := by rw [← hab]; group
        rw [this]
        exact (⨆ i ∈ Finset.univ.erase j, S i).mul_mem (hall j)
          ((⨆ i ∈ Finset.univ.erase j, S i).inv_mem hbj)
      have ha1 : a ∈ S j ⊓ ⨆ i ∈ Finset.univ.erase j, S i := ⟨ha, han⟩
      rw [h.indep j _ (Finset.notMem_erase j _), Subgroup.mem_bot] at ha1
      rw [ha1, one_mul] at hab
      rw [← hab]
      exact hb
  simpa using hind Finset.univ

theorem PermProd.oddCoreIn_fixed_eq_bot (h : PermProd S σ π)
    (hfix : ∀ i, π i = i → oddCoreIn (S i ⊓ fixedSubgroup σ) = ⊥)
    (hswap : ∀ i, π i ≠ i → oddCoreIn (S i) = ⊥) : oddCoreIn (fixedSubgroup σ) = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  refine h.eq_one_of_mem_all_erase fun k => ?_
  by_cases hk : π k = k
  · exact h.mem_erase_of_fixed hfix hn hk
  · exact h.mem_erase_of_swap hswap hn hk

end Key

theorem oddCoreIn_fixed_eq_bot_of_permProd {G : Type} [Group G] [Finite G] {ι : Type} [Finite ι]
    {S : ι → Subgroup G} {σ : MulAut G} {π : ι → ι} (h : PermProd S σ π)
    (hfix : ∀ i, π i = i → oddCoreIn (S i ⊓ fixedSubgroup σ) = ⊥)
    (hswap : ∀ i, π i ≠ i → oddCoreIn (S i) = ⊥) : oddCoreIn (fixedSubgroup σ) = ⊥ := by
  classical
  have := Fintype.ofFinite ι
  exact h.oddCoreIn_fixed_eq_bot hfix hswap

section Quotient

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_fixed_le_center_of_quotient (σ : MulAut X)
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient X σ)) = ⊥) :
    oddCoreIn (fixedSubgroup σ) ≤ Subgroup.center X := by
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  set C := fixedSubgroup σ with hC
  set C' := fixedSubgroup (autToCentralQuotient X σ) with hC'
  have key : ∀ y : X, π y ∈ C' → ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have hy' : (QuotientGroup.mk (σ y) : X ⧸ Subgroup.center X) = QuotientGroup.mk y := hy
    obtain ⟨z, hzdef⟩ : ∃ z, z = y⁻¹ * σ y := ⟨_, rfl⟩
    have hz : z ∈ Subgroup.center X := hzdef ▸ QuotientGroup.eq.mp hy'.symm
    have hσy : σ y = y * z := by rw [hzdef]; group
    have hzc := Subgroup.mem_center_iff.mp hz
    have hσc : σ c = c := hc
    show σ (y * c * y⁻¹) = y * c * y⁻¹
    rw [map_mul, map_mul, map_inv, hσc, hσy]
    calc y * z * c * (y * z)⁻¹ = y * (z * c) * z⁻¹ * y⁻¹ := by group
      _ = y * (c * z) * z⁻¹ * y⁻¹ := by rw [← hzc c]
      _ = y * c * y⁻¹ := by group
  have hnorm : ∀ y : X, π y ∈ C' → y ∈ Subgroup.normalizer (C : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key y hy c hc, fun hc => ?_⟩
    have hy' : π y⁻¹ ∈ C' := by rw [map_inv]; exact C'.inv_mem hy
    have := key y⁻¹ hy' _ hc
    simpa [mul_assoc] using this
  have hCC' : C.map π ≤ C' := by
    rintro _ ⟨c, hc, rfl⟩
    have hσc : σ c = c := hc
    show autToCentralQuotient X σ (QuotientGroup.mk c) = QuotientGroup.mk c
    rw [autToCentralQuotient_mk, hσc]
  have hS : (oddCoreIn C).map π ≤ oddCoreIn C' := by
    refine le_oddCoreIn_of_normalizes ((Subgroup.map_mono (oddCoreIn_le C)).trans hCC') ?_
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_map_dvd _ π))
    intro c' hc'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) c'
    have hyO : y ∈ Subgroup.normalizer (oddCoreIn C : Set X) :=
      mem_normalizer_oddCoreIn_of_mem_normalizer (hnorm y hc')
    have fwd : ∀ y : X, y ∈ Subgroup.normalizer (oddCoreIn C : Set X) →
        ∀ x ∈ (oddCoreIn C).map π, π y * x * (π y)⁻¹ ∈ (oddCoreIn C).map π := by
      intro y hy
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨y * s * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy s).mp hs, by simp⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => fwd y hyO x hx, fun hx => ?_⟩
    have := fwd y⁻¹ ((Subgroup.normalizer (oddCoreIn C : Set X)).inv_mem hyO) _ hx
    rw [map_inv] at this
    have e : (π y)⁻¹ * (π y * x * (π y)⁻¹) * ((π y)⁻¹)⁻¹ = x := by group
    rwa [e] at this
  rw [h, le_bot_iff] at hS
  intro s hs
  have : π s ∈ (oddCoreIn C).map π := ⟨s, hs, rfl⟩
  rw [hS, Subgroup.mem_bot] at this
  exact (QuotientGroup.ker_mk' (Subgroup.center X)) ▸ this

theorem oddCoreIn_fixed_eq_bot_of_quotient (hO : oddCoreIn (⊤ : Subgroup X) = ⊥) (σ : MulAut X)
    (h : oddCoreIn (fixedSubgroup (autToCentralQuotient X σ)) = ⊥) :
    oddCoreIn (fixedSubgroup σ) = ⊥ := by
  have h1 := oddCoreIn_fixed_le_center_of_quotient σ h
  have h2 := le_oddCoreIn_top_of_le_center h1 (odd_card_oddCoreIn _)
  rw [hO] at h2
  exact le_bot_iff.mp h2

omit [Finite X] in
theorem map_autToCentralQuotient (σ : MulAut X) (S : Subgroup X) :
    (S.map (QuotientGroup.mk' (Subgroup.center X))).map
        (autToCentralQuotient X σ : (X ⧸ Subgroup.center X) →* (X ⧸ Subgroup.center X)) =
      (S.map (σ : X →* X)).map (QuotientGroup.mk' (Subgroup.center X)) := by
  have : (autToCentralQuotient X σ : (X ⧸ Subgroup.center X) →* (X ⧸ Subgroup.center X)).comp
      (QuotientGroup.mk' (Subgroup.center X)) =
      (QuotientGroup.mk' (Subgroup.center X)).comp (σ : X →* X) :=
    MonoidHom.ext fun x => rfl
  rw [Subgroup.map_map, Subgroup.map_map, this]

end Quotient

theorem oddCoreIn_top_quotient_eq_bot (Y : Type) [Group Y] [Finite Y] :
    oddCoreIn (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y)) = ⊥ := by
  have hS : (oddCoreIn (⊤ : Subgroup (Y ⧸ classicalInvolutionOddCore Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
  have h2 := CFSG.ComponentClassification.OddCore.maximal (Y ⧸ classicalInvolutionOddCore Y)
    (oddCoreIn ⊤) hS (odd_card_oddCoreIn _)
  have hcf : componentClassificationOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  rw [hcf] at h2
  exact le_bot_iff.mp h2

section Transport

variable {G A : Type} [Group G] [Group A]

theorem oddCoreIn_inf_fixed_eq_bot_of_equiv {S : Subgroup G} (e : A ≃* ↥S) (hA : FixedOddFree A)
    (σ : MulAut G) (hσ : σ * σ = 1) (hS : S.map (σ : G →* G) = S) :
    oddCoreIn (S ⊓ fixedSubgroup σ) = ⊥ := by
  set σS : MulAut ↥S := (MulEquiv.subgroupMap σ S).trans (MulEquiv.subgroupCongr hS) with hσS
  have hσSapp : ∀ x : ↥S, ((σS x : ↥S) : G) = σ (x : G) := fun x => rfl
  have hσS2 : σS * σS = 1 := by
    ext x
    show ((σS (σS x) : ↥S) : G) = (x : G)
    rw [hσSapp, hσSapp]
    exact apply_apply_of_mul_eq_one hσ _
  set ρ : MulAut A := MulAut.congr e.symm σS with hρ
  have hρ2 : ρ * ρ = 1 := by
    rw [hρ, ← map_mul, hσS2, map_one]
  have hcongr : MulAut.congr e ρ = σS := by
    refine MulEquiv.ext fun x => ?_
    show e (ρ (e.symm x)) = σS x
    simp [hρ, MulAut.congr_apply]
  have h1 := oddCoreIn_fixed_congr_eq_bot' e ρ (hA ρ hρ2)
  rw [hcongr] at h1
  have hmap : (fixedSubgroup σS).map S.subtype = S ⊓ fixedSubgroup σ := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val (mem_fixedSubgroup_iff.mp hy)⟩
    · rintro ⟨hxS, hx⟩
      exact ⟨⟨x, hxS⟩, Subtype.ext (mem_fixedSubgroup_iff.mp hx), rfl⟩
  have h2 := map_oddCoreIn_subtype (Y := S) (fixedSubgroup σS)
  rw [hmap, h1, Subgroup.map_bot] at h2
  exact h2.symm

theorem oddCoreIn_eq_bot_of_equiv {S : Subgroup G} (e : A ≃* ↥S) (hA : FixedOddFree A) :
    oddCoreIn S = ⊥ := by
  have h := oddCoreIn_inf_fixed_eq_bot_of_equiv e hA (1 : MulAut G) (by simp)
    (by ext x; simp)
  have hf : fixedSubgroup (1 : MulAut G) = ⊤ := by
    ext x
    simp [mem_fixedSubgroup_iff]
  rwa [hf, inf_top_eq] at h

end Transport

end CFSG.ClassicalInvolution.Q3.Q3NM
