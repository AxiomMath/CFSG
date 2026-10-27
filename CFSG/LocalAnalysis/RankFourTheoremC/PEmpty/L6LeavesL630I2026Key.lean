module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Claim

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

section Helpers

variable {G : Type} [Group G]

theorem comm_mul_right_of_central {u s s' : G}
    (h : u * s' * u⁻¹ * s'⁻¹ ∈ Subgroup.center G) :
    u * (s * s') * u⁻¹ * (s * s')⁻¹ = (u * s * u⁻¹ * s⁻¹) * (u * s' * u⁻¹ * s'⁻¹) := by
  have hc := Subgroup.mem_center_iff.mp h s⁻¹
  calc u * (s * s') * u⁻¹ * (s * s')⁻¹
      = (u * s * u⁻¹) * (u * s' * u⁻¹ * s'⁻¹) * s⁻¹ := by group
    _ = (u * s * u⁻¹) * (s⁻¹ * (u * s' * u⁻¹ * s'⁻¹)) := by rw [hc]; group
    _ = _ := by group

theorem comm_inv_right_of_central {u s : G} (h : u * s * u⁻¹ * s⁻¹ ∈ Subgroup.center G) :
    u * s⁻¹ * u⁻¹ * s⁻¹⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h) s⁻¹
  calc u * s⁻¹ * u⁻¹ * s⁻¹⁻¹ = s⁻¹ * (u * s * u⁻¹ * s⁻¹)⁻¹ * s := by group
    _ = (u * s * u⁻¹ * s⁻¹)⁻¹ * s⁻¹ * s := by rw [hc]
    _ = _ := by group

theorem exists_mul_central {S Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) {h : G}
    (hh : h ∈ S ⊔ Z) : ∃ s ∈ S, ∃ c ∈ Z, h = s * c :=
  exists_mul_of_comm_sup (fun s _ c hc => Subgroup.mem_center_iff.mp (hZ hc) s) hh

end Helpers

section TrivSub

variable {G : Type} [Group G]

@[expose] def trivSub (S K Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) : Subgroup G where
  carrier := {s | s ∈ S ∧ ∀ u ∈ K, u * s * u⁻¹ * s⁻¹ ∈ Z}
  one_mem' := ⟨S.one_mem, fun u _ => by simpa using Z.one_mem⟩
  mul_mem' := by
    rintro s s' ⟨hsS, hsK⟩ ⟨hsS', hsK'⟩
    refine ⟨S.mul_mem hsS hsS', fun u hu => ?_⟩
    rw [comm_mul_right_of_central (hZ (hsK' u hu))]
    exact Z.mul_mem (hsK u hu) (hsK' u hu)
  inv_mem' := by
    rintro s ⟨hsS, hsK⟩
    refine ⟨S.inv_mem hsS, fun u hu => ?_⟩
    rw [comm_inv_right_of_central (hZ (hsK u hu))]
    exact Z.inv_mem (hsK u hu)

theorem trivSub_le {S K Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) : trivSub S K Z hZ ≤ S :=
  fun _ hs => hs.1

theorem trivSub_conj {S K Z P : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    (hPS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S) (hPK : ∀ p ∈ P, ∀ u ∈ K, p * u * p⁻¹ ∈ K) :
    ∀ p ∈ P, ∀ s ∈ trivSub S K Z hZ, p * s * p⁻¹ ∈ trivSub S K Z hZ := by
  intro p hp s hs
  obtain ⟨hsS, hsK⟩ := hs
  refine ⟨hPS p hp s hsS, fun u hu => ?_⟩
  have hu' : p⁻¹ * u * p ∈ K := by simpa using hPK p⁻¹ (P.inv_mem hp) u hu
  have h1 := hsK _ hu'
  have h2 : u * (p * s * p⁻¹) * u⁻¹ * (p * s * p⁻¹)⁻¹ =
      p * ((p⁻¹ * u * p) * s * (p⁻¹ * u * p)⁻¹ * s⁻¹) * p⁻¹ := by group
  rw [h2, Subgroup.mem_center_iff.mp (hZ h1) p]
  simpa using h1

theorem trivSub_eq [Finite G] {S P K Z : Subgroup G} {α β γ δ z : G}
    (hpres : QDPres S α β γ δ z) (hzc : z ∈ Subgroup.center G) (hZ : Z ≤ Subgroup.center G)
    (hzZ : z ∈ Z) (hP5 : Nat.card P = 5) (hPS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S)
    (hPK : ∀ p ∈ P, ∀ u ∈ K, p * u * p⁻¹ ∈ K) (hnc : ¬ ∀ p ∈ P, ∀ s ∈ S, p * s = s * p)
    (hex : ∃ s ∈ S, s ≠ 1 ∧ s ≠ z ∧ ∀ u ∈ K, u * s * u⁻¹ * s⁻¹ ∈ Z) :
    trivSub S K Z hZ = S := by
  have hF : ∀ p ∈ P, ∀ s ∈ trivSub S K Z hZ, p * s * p⁻¹ ∈ trivSub S K Z hZ :=
    trivSub_conj hZ hPS hPK
  haveI : Finite (trivSub S K Z hZ) := inferInstance
  have hmod := card_modEq_conj hP5 hF
  have hzF : z ∈ trivSub S K Z hZ :=
    ⟨hpres.z_mem, fun u _ => by
      have := Subgroup.mem_center_iff.mp hzc u
      rw [this]
      simpa using Z.one_mem⟩
  have hfix : trivSub S K Z hZ ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro s hs
      obtain ⟨hsF, hsC⟩ := Subgroup.mem_inf.mp hs
      have hsC' := Subgroup.mem_centralizer_iff.mp hsC
      rcases fixed_of_pres hP5 hPS hpres hzc hnc s hsF.1 (fun p hp => hsC' p hp) with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨hzF, Subgroup.mem_centralizer_iff.mpr (fun p _ => ?_)⟩
      exact Subgroup.mem_center_iff.mp hzc p
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hpres.zz
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hpres.z_ne]
  rw [hfix, hzcard] at hmod
  rcases eq_zpowers_or_eq hpres (trivSub_le hZ) hzF hmod with h | h
  · exfalso
    obtain ⟨s, hsS, hs1, hsz, hsK⟩ := hex
    have hsF : s ∈ trivSub S K Z hZ := ⟨hsS, hsK⟩
    rw [h] at hsF
    exact (mem_zpowers_of_sq_one hz2 hpres.z_ne hsF).elim hs1 hsz
  · exact h

theorem exists_fixed_noncentral [Finite G] {S K Z : Subgroup G} {α β γ δ z : G}
    (hpres : QDPres S α β γ δ z) (hZ : Z ≤ Subgroup.center G) (hzZ : z ∈ Z)
    (hKp : IsPGroup 2 K) (hSK : S ≤ K) (hZK : Z ≤ K)
    (hKN : K ≤ Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G)) :
    ∃ s ∈ S, s ≠ 1 ∧ s ≠ z ∧ ∀ u ∈ K, u * s * u⁻¹ * s⁻¹ ∈ Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHK : S ⊔ Z ≤ K := sup_le hSK hZK
  let ZK : Subgroup ↥K := Z.subgroupOf K
  haveI hZKn : ZK.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ Z := hn
    show ((g * n * g⁻¹ : ↥K) : G) ∈ Z
    have h1 := Subgroup.mem_center_iff.mp (hZ hn') (g : G)
    have h2 : ((g * n * g⁻¹ : ↥K) : G) = (n : G) := by
      show (g : G) * (n : G) * (g : G)⁻¹ = (n : G)
      rw [h1]
      group
    rw [h2]
    exact hn'⟩
  have hQp : IsPGroup 2 (↥K ⧸ ZK) := hKp.to_quotient ZK
  haveI : Group.IsNilpotent (↥K ⧸ ZK) := hQp.isNilpotent
  let Hs : Subgroup ↥K := (S ⊔ Z).subgroupOf K
  haveI hHsn : Hs.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  let Hb : Subgroup (↥K ⧸ ZK) := Hs.map (QuotientGroup.mk' ZK)
  haveI : Hb.Normal := hHsn.map _ (QuotientGroup.mk'_surjective ZK)
  have hsHs : ∀ s, ∀ hs : s ∈ S, (⟨s, hSK hs⟩ : ↥K) ∈ Hs := fun s hs =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hs)
  have hHb : Hb ≠ ⊥ := by
    intro h0
    have hS : ∀ s ∈ S, s ∈ Z := by
      intro s hs
      have h1 : QuotientGroup.mk' ZK ⟨s, hSK hs⟩ ∈ Hb := Subgroup.mem_map_of_mem _ (hsHs s hs)
      rw [h0, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
    have h1 := hpres.βα
    have h2 := Subgroup.mem_center_iff.mp (hZ (hS _ hpres.β_mem)) α
    rw [h2] at h1
    apply hpres.z_ne
    have h3 : 1 * (β * α) = z * (β * α) := by rw [one_mul]; exact h1
    exact (mul_right_cancel h3).symm
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHb)
  have hxHb : (x : ↥K ⧸ ZK) ∈ Hb := (Subgroup.mem_inf.mp x.2).1
  have hxc : (x : ↥K ⧸ ZK) ∈ Subgroup.center (↥K ⧸ ZK) := (Subgroup.mem_inf.mp x.2).2
  obtain ⟨k, hkHs, hkx⟩ := Subgroup.mem_map.mp hxHb
  have hk : (k : G) ∈ S ⊔ Z := Subgroup.mem_subgroupOf.mp hkHs
  have hkcomm : ∀ u ∈ K, u * (k : G) * u⁻¹ * (k : G)⁻¹ ∈ Z := by
    intro u hu
    have h1 := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk' ZK ⟨u, hu⟩)
    rw [← hkx, ← map_mul, ← map_mul] at h1
    have h2 := QuotientGroup.eq_iff_div_mem.mp h1
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using h3
  have hkZ : (k : G) ∉ Z := by
    intro hkZ
    apply hx1
    apply Subtype.ext
    show (x : ↥K ⧸ ZK) = 1
    rw [← hkx]
    exact (QuotientGroup.eq_one_iff k).mpr (Subgroup.mem_subgroupOf.mpr hkZ)
  obtain ⟨s, hsS, c, hcZ, hkeq⟩ := exists_mul_central hZ hk
  refine ⟨s, hsS, ?_, ?_, ?_⟩
  · intro h
    apply hkZ
    rw [hkeq, h, one_mul]
    exact hcZ
  · intro h
    apply hkZ
    rw [hkeq, h]
    exact Z.mul_mem hzZ hcZ
  · intro u hu
    have hs : s = (k : G) * c⁻¹ := by rw [hkeq]; group
    have hcc := Subgroup.mem_center_iff.mp (hZ (Z.inv_mem hcZ)) u⁻¹
    have h4 : u * s * u⁻¹ * s⁻¹ = u * (k : G) * u⁻¹ * (k : G)⁻¹ := by
      rw [hs]
      calc u * ((k : G) * c⁻¹) * u⁻¹ * ((k : G) * c⁻¹)⁻¹
          = u * (k : G) * (c⁻¹ * u⁻¹) * c * (k : G)⁻¹ := by group
        _ = u * (k : G) * (u⁻¹ * c⁻¹) * c * (k : G)⁻¹ := by rw [← hcc]
        _ = _ := by group
    rw [h4]
    exact hkcomm u hu

end TrivSub

section KeyLemma

variable {G : Type} [Group G]

theorem key_lemma [Finite G] {S T P : Subgroup G} {α β γ δ z : G}
    (hpres : QDPres S α β γ δ z) (hzc : z ∈ Subgroup.center G)
    (hC : ∀ g : G, (∀ s ∈ S, g * s = s * g) → g ∈ Subgroup.center G)
    (hsz : ∀ c ∈ Subgroup.center G, c * c = 1 → c = 1 ∨ c = z)
    (hT : IsPGroup 2 T) (hST : S ≤ T) (hP5 : Nat.card P = 5)
    (hPS : ∀ p ∈ P, ∀ s ∈ S, p * s * p⁻¹ ∈ S) (hPT : ∀ p ∈ P, ∀ t ∈ T, p * t * p⁻¹ ∈ T)
    (hnc : ¬ ∀ p ∈ P, ∀ s ∈ S, p * s = s * p) :
    ∀ t ∈ T, ∃ s ∈ S, s⁻¹ * t ∈ Subgroup.center G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup G, Z = T ⊓ Subgroup.center G := ⟨_, rfl⟩
  have hZc : Z ≤ Subgroup.center G := by rw [hZdef]; exact inf_le_right
  have hZT : Z ≤ T := by rw [hZdef]; exact inf_le_left
  have hzZ : z ∈ Z := by rw [hZdef]; exact Subgroup.mem_inf.mpr ⟨hST hpres.z_mem, hzc⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = S ⊔ Z := ⟨_, rfl⟩
  have hSH : S ≤ H := by rw [hHdef]; exact le_sup_left
  have hZH : Z ≤ H := by rw [hHdef]; exact le_sup_right
  have hHT : H ≤ T := by rw [hHdef]; exact sup_le hST hZT
  have hPH : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H := by
    intro p hp h hh
    rw [hHdef] at hh
    obtain ⟨s, hs, c, hc, rfl⟩ := exists_mul_central hZc hh
    have hcp := Subgroup.mem_center_iff.mp (hZc hc) p⁻¹
    have h1 : p * (s * c) * p⁻¹ = (p * s * p⁻¹) * c := by
      calc p * (s * c) * p⁻¹ = p * s * (c * p⁻¹) := by group
        _ = p * s * (p⁻¹ * c) := by rw [← hcp]
        _ = (p * s * p⁻¹) * c := by group
    rw [h1, hHdef]
    exact Subgroup.mul_mem_sup (hPS p hp s hs) hc
  have hPN : ∀ p ∈ P, p ∈ Subgroup.normalizer (H : Set G) := by
    intro p hp
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hPH p hp h hh
    · intro hh
      have := hPH p⁻¹ (P.inv_mem hp) _ hh
      simpa [mul_assoc] using this
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G, K = T ⊓ Subgroup.normalizer (H : Set G) := ⟨_, rfl⟩
  have hKT : K ≤ T := by rw [hKdef]; exact inf_le_left
  have hKN : K ≤ Subgroup.normalizer (H : Set G) := by rw [hKdef]; exact inf_le_right
  have hPK : ∀ p ∈ P, ∀ u ∈ K, p * u * p⁻¹ ∈ K := by
    intro p hp u hu
    rw [hKdef]
    refine Subgroup.mem_inf.mpr ⟨hPT p hp u (hKT hu), ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hPN p hp) (hKN hu))
      (Subgroup.inv_mem _ (hPN p hp))
  have hSK : S ≤ K := fun s hs => by
    rw [hKdef]
    exact Subgroup.mem_inf.mpr ⟨hST hs, Subgroup.le_normalizer (hSH hs)⟩
  have hZK : Z ≤ K := fun c hc => by
    rw [hKdef]
    exact Subgroup.mem_inf.mpr ⟨hZT hc, Subgroup.le_normalizer (hZH hc)⟩
  have hKp : IsPGroup 2 K := hT.to_le hKT
  have hHN : K ≤ Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G) := by
    rw [← hHdef]
    exact hKN
  have hex := exists_fixed_noncentral hpres hZc hzZ hKp hSK hZK hHN
  have hF : trivSub S K Z hZc = S := trivSub_eq hpres hzc hZc hzZ hP5 hPS hPK hnc hex
  have claimA : ∀ u ∈ K, ∀ s ∈ S, u * s * u⁻¹ * s⁻¹ ∈ Z := by
    intro u hu s hs
    have hs' : s ∈ trivSub S K Z hZc := by rw [hF]; exact hs
    exact hs'.2 u hu
  have hKH : ∀ u ∈ K, u ∈ H := by
    intro u hu
    have hmem : u ∈ commNormalizer S := fun s hs => hZc (claimA u hu s hs)
    obtain ⟨s₀, hs₀, hc⟩ := claimB hpres hzc hC hsz hmem
    have hT' : u * s₀⁻¹ ∈ T := T.mul_mem (hKT hu) (T.inv_mem (hST hs₀))
    have hZu : u * s₀⁻¹ ∈ Z := by rw [hZdef]; exact Subgroup.mem_inf.mpr ⟨hT', hc⟩
    have h2 : u = (u * s₀⁻¹) * s₀ := by group
    rw [h2]
    exact H.mul_mem (hZH hZu) (hSH hs₀)
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnc' : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  have hfull : H.subgroupOf T = ⊤ := by
    apply (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc') (H.subgroupOf T)
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_set_normalizer_iff] at hu
      have huN : (u : G) ∈ Subgroup.normalizer (H : Set G) := by
        rw [Subgroup.mem_set_normalizer_iff]
        intro h
        constructor
        · intro hh
          have h1 := (hu ⟨h, hHT hh⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
          exact Subgroup.mem_subgroupOf.mp h1
        · intro hh
          have hhT : u * h * u⁻¹ ∈ T := hHT hh
          have hhT' : h ∈ T := by
            have := T.mul_mem (T.mul_mem (T.inv_mem u.2) hhT) u.2
            simpa [mul_assoc] using this
          have h1 := (hu ⟨h, hhT'⟩).mpr (Subgroup.mem_subgroupOf.mpr hh)
          exact Subgroup.mem_subgroupOf.mp h1
      exact Subgroup.mem_subgroupOf.mpr
        (hKH (u : G) (by rw [hKdef]; exact Subgroup.mem_inf.mpr ⟨u.2, huN⟩))
    · exact Subgroup.le_normalizer
  intro t ht
  have hmem : (⟨t, ht⟩ : ↥T) ∈ H.subgroupOf T := by rw [hfull]; trivial
  have htH : t ∈ H := Subgroup.mem_subgroupOf.mp hmem
  rw [hHdef] at htH
  obtain ⟨s, hs, c, hc, hsc⟩ := exists_mul_central hZc htH
  refine ⟨s, hs, ?_⟩
  have : s⁻¹ * t = c := by rw [hsc]; group
  rw [this]
  exact hZc hc

end KeyLemma

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026
