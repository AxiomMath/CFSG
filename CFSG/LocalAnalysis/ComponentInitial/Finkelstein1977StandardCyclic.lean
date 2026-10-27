module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Configuration
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Local
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement

public section

namespace CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise

@[expose] def HypothesisOne (Y : Type*) [Group Y] : Prop :=
  ∀ M : Subgroup (MulAut Y), (MulAut.conj : Y →* MulAut Y).range ≤ M →
    ∀ x ∈ M, orderOf x = 2 →
      ∀ B : Subgroup ((M ⊓ Subgroup.centralizer ({x} : Set (MulAut Y)) : Subgroup (MulAut Y)) ⧸
          CFSG.Assembly.oddCore
            (M ⊓ Subgroup.centralizer ({x} : Set (MulAut Y)) : Subgroup (MulAut Y))),
        B.Normal → ¬ (Nonempty (B ≃* Multiplicative (ZMod 4)) ∨
          Nonempty (B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))

section Automizer

variable {G : Type*} [Group G]

@[expose] noncomputable def automizer (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) :=
  (centerQuotientHom L).comp L.normalizerMonoidHom

theorem automizer_apply_mk (L : Subgroup G) (n : Subgroup.normalizer (L : Set G)) (l : L) :
    automizer L n (l : L ⧸ Subgroup.center L) =
      ((⟨n * l * n⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 l).mp l.2⟩ : L) :
        L ⧸ Subgroup.center L) := by
  change onCenterQuotient (L.normalizerMonoidHom n) (QuotientGroup.mk' _ l) = _
  rw [onCenterQuotient_apply_mk]
  rfl

theorem automizer_eq_one_iff (L : Subgroup G) [Group.IsPerfect L]
    (n : Subgroup.normalizer (L : Set G)) :
    automizer L n = 1 ↔ (n : G) ∈ Subgroup.centralizer (L : Set G) := by
  have hker : ∀ m : Subgroup.normalizer (L : Set G),
      L.normalizerMonoidHom m = 1 ↔ (m : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro m
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    apply (hker n).mp
    apply centerQuotientHom_injective L
    rw [map_one]
    exact h
  · intro h
    change centerQuotientHom L (L.normalizerMonoidHom n) = 1
    rw [(hker n).mpr h, map_one]

theorem conj_range_le_automizer_range (L : Subgroup G) :
    (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      (automizer L).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨⟨l, Subgroup.le_normalizer l.2⟩, ?_⟩
  ext w
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  rw [automizer_apply_mk, MulAut.conj_apply]
  rfl

end Automizer

theorem not_hypothesisOne_of_full_conj {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (hS : IsCyclic S) (hS4 : 4 ≤ Nat.card S)
    {g : G} (hg : g ∉ Subgroup.normalizer (L : Set G)) {R T : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer (L : Set G)) (hR : IsPGroup 2 R)
    (hRcard : Nat.card R = Nat.card S)
    (hTg : T ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hTcard : Nat.card T = Nat.card S) (hRT : R ≤ Subgroup.centralizer (T : Set G)) :
    ¬ HypothesisOne (L ⧸ Subgroup.center L) := by
  classical
  intro hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (L : Set G) → IsPGroup 2 P →
      IsCyclic P ∧ Nat.card P ≤ Nat.card S := fun P hPC hP => isCyclic_and_card_le_of_le S hS hPC hP
  have hmaxg : ∀ P : Subgroup G,
      P ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom → IsPGroup 2 P →
      IsCyclic P ∧ Nat.card P ≤ Nat.card S :=
    fun P hPC hP => isCyclic_and_card_le_of_le_conj S hS hPC hP
  generalize Nat.card S = m at hS4 hRcard hTcard hmax hmaxg
  clear hS S
  have hL' := hL
  obtain ⟨hq, -, hodd, hNC, -⟩ := hL'
  have : Group.IsPerfect L := ⟨hq.1⟩
  set C := Subgroup.centralizer (L : Set G) with hCdef
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Cg := C.map (MulAut.conj g).toMonoidHom with hCgdef
  have hCN : C ≤ N := hNC ▸ Subgroup.le_normalizer
  have hgC : g ∉ Subgroup.normalizer (C : Set G) := by rwa [hNC]
  have hCCg : ∀ y ∈ C, y ∈ Cg → ∀ k : ℕ, orderOf y = 2 ^ k → y = 1 := by
    intro y hyC hyCg k hk
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hyC, hyCg⟩)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr (hodd g hgC))
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hT2 : ∀ y ∈ T, ∃ k : ℕ, orderOf y = 2 ^ k := fun y hy => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hy⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have hTC : ∀ y ∈ T, y ∈ C → y = 1 := fun y hyT hyC => by
    obtain ⟨k, hk⟩ := hT2 y hyT
    exact hCCg y hyC (hTg hyT) k hk
  have hTcyc : IsCyclic T := (hmaxg T hTg hT).1
  obtain ⟨⟨s, hsT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hsord : orderOf s = m := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk, hTcard] at h
  have h4m : 4 ∣ m := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    rw [hTcard] at hn
    have hn2 : 2 ≤ n := by
      by_contra h
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hn, show 4 = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hn2
  set u := s ^ (m / 4) with hudef
  have huT : u ∈ T := Subgroup.pow_mem _ hsT _
  have hu4 : orderOf u = 4 := by
    rw [hudef, orderOf_pow_of_dvd (by omega) (by rw [hsord]; exact Nat.div_dvd_of_dvd h4m), hsord]
    exact Nat.div_div_self h4m (by omega)
  set t := u ^ 2 with htdef
  have htT : t ∈ T := Subgroup.pow_mem _ huT 2
  have htN : t ∈ N := hTN htT
  have htord : orderOf t = 2 := by
    rw [htdef, orderOf_pow_of_dvd (by norm_num) (by rw [hu4]; norm_num), hu4]
  have htt : t * t = 1 := by rw [← sq, ← htord, pow_orderOf_eq_one]
  have htC : t ∉ C := fun h => by
    have := hTC t htT h
    rw [this, orderOf_one] at htord
    omega
  have hsTzp : ∀ y ∈ T, ∃ k : ℤ, s ^ k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hsTzp a ha
    obtain ⟨j, rfl⟩ := hsTzp b hb
    exact (Commute.zpow_zpow_self s i j).eq
  have hRcyc : IsCyclic R := (hmax R hRC hR).1
  have hRm : ∀ P : Subgroup G, P ≤ C → IsPGroup 2 P → Nat.card P ≤ Nat.card R := by
    intro P hPC hP
    rw [hRcard]
    exact (hmax P hPC hP).2
  have htR : ∀ r ∈ R, t * r = r * t := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp (hRT hr) t htT)
  obtain ⟨z, hzR, hz2, hinv⟩ :
      ∃ z ∈ R, z * z = 1 ∧ ∀ w ∈ R, w * w = 1 → w = 1 ∨ w = z := by
    by_cases h : ∃ z ∈ R, orderOf z = 2
    · obtain ⟨z, hzR, hz⟩ := h
      refine ⟨z, hzR, by rw [← sq, ← hz, pow_orderOf_eq_one], fun w hw hww => ?_⟩
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · exact Or.inr (eq_of_orderOf_eq_two_of_isCyclic hRcyc hw hzR
          (orderOf_eq_prime (by rw [sq, hww]) hw1) hz)
    · refine ⟨1, Subgroup.one_mem _, mul_one 1, fun w hw hww => Or.inl ?_⟩
      by_contra hw1
      exact h ⟨w, hw, orderOf_eq_prime (by rw [sq, hww]) hw1⟩
  have htNC : t ∈ Subgroup.normalizer (C : Set G) := hNC ▸ htN
  set π := automizer L with hπdef
  have hπker : ∀ n : N, π n = 1 ↔ (n : G) ∈ C := fun n => automizer_eq_one_iff L n
  set tN : N := ⟨t, htN⟩ with htNdef
  set x := π tN with hxdef
  have hxord : orderOf x = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← map_mul]
      exact (hπker _).mpr (by
        change t * t ∈ C
        rw [htt]
        exact C.one_mem)
    · intro h
      exact htC ((hπker tN).mp h)
  set M := π.range with hMdef
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      M := conj_range_le_automizer_range L
  have hxM : x ∈ M := ⟨tN, rfl⟩
  set Cx : Subgroup (MulAut (L ⧸ Subgroup.center L)) :=
    M ⊓ Subgroup.centralizer ({x} : Set (MulAut (L ⧸ Subgroup.center L))) with hCxdef
  have hmemCx : ∀ n : N, (n : G) * t = t * n → π n ∈ Cx := by
    intro n hn
    refine ⟨⟨n, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hxdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hn
  have hlift : ∀ a ∈ Cx, ∃ n : N, π n = a ∧
      ((n : G) * t * (n : G)⁻¹ = t ∨ (n : G) * t * (n : G)⁻¹ = t * z) := by
    intro a ha
    obtain ⟨⟨n₀, rfl⟩, hcomm⟩ := ha
    have hcomm' : π (n₀ * tN * n₀⁻¹ * tN⁻¹) = 1 := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hcomm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxdef, h]
      group
    have hk : t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹) ∈ C := by
      have h1 : (n₀ : G) * t * (n₀ : G)⁻¹ * t⁻¹ ∈ C := (hπker _).mp hcomm'
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htNC) _).mp h1
      rw [inv_inv] at h2
      simpa [mul_assoc] using h2
    have hj : (t * (t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹))) *
        (t * (t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹))) = 1 := by
      calc (t * (t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹))) *
            (t * (t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹))) = (n₀ : G) * (t * t) * (n₀ : G)⁻¹ := by
            group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    obtain ⟨c, hcC, hc⟩ := exists_conj_eq_of_mul_self_eq_one htC htt htNC hRC hR hRm htR hinv hk hj
    refine ⟨⟨c, hCN hcC⟩ * n₀, ?_, ?_⟩
    · rw [map_mul, (hπker _).mpr hcC, one_mul]
    · have e : t * (t⁻¹ * ((n₀ : G) * t * (n₀ : G)⁻¹)) = (n₀ : G) * t * (n₀ : G)⁻¹ := by group
      rw [e] at hc
      simpa [mul_assoc] using hc
  set C₀ : Subgroup (MulAut (L ⧸ Subgroup.center L)) :=
    ((Subgroup.centralizer ({t} : Set G)).subgroupOf N).map π with hC₀def
  have hmemC₀ : ∀ n : N, (n : G) * t = t * n → π n ∈ C₀ := fun n hn =>
    ⟨n, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hn), rfl⟩
  have hC₀Cx : C₀ ≤ Cx := by
    rintro _ ⟨n, hn, rfl⟩
    exact hmemCx n (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hn))
  have hcomm_of : ∀ y : G, y * t * y⁻¹ = t → y * t = t * y := fun y h => by
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [h]
  have hout : ∀ a ∈ Cx, a ∉ C₀ → ∃ n : N, π n = a ∧ (n : G) * t * (n : G)⁻¹ = t * z := by
    intro a ha haC₀
    obtain ⟨n, rfl, hn | hn⟩ := hlift a ha
    · exact absurd (hmemC₀ n (hcomm_of _ hn)) haC₀
    · exact ⟨n, rfl, hn⟩
  have hmulC₀ : ∀ a b : Cx, a ∉ C₀.subgroupOf Cx → b ∉ C₀.subgroupOf Cx →
      a * b ∈ C₀.subgroupOf Cx := by
    intro a b ha hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    obtain ⟨na, hna, hnat⟩ := hout a a.2 ha
    obtain ⟨nb, hnb, hnbt⟩ := hout b b.2 hb
    obtain ⟨n, hn, hn' | hn'⟩ := hlift _ (a * b).2
    · exact hn ▸ hmemC₀ n (hcomm_of _ hn')
    ·
      exfalso
      apply ha
      have hy : ((na * nb : N) : G) * t * ((na * nb : N) : G)⁻¹ =
          (na : G) * (t * z) * (na : G)⁻¹ := by
        rw [← hnbt]
        push_cast
        group
      have hc : ((n * (na * nb)⁻¹ : N) : G) ∈ C := by
        rw [← hπker, map_mul, map_inv, map_mul, hn, hna, hnb, Subgroup.coe_mul, mul_inv_cancel]
      set c : G := ((n * (na * nb)⁻¹ : N) : G) with hcdef
      have hcy : c * ((na : G) * (t * z) * (na : G)⁻¹) * c⁻¹ = (na : G) * t * (na : G)⁻¹ := by
        rw [← hy, hnat]
        have : c * ((na * nb : N) : G) = (n : G) := by
          rw [hcdef]
          push_cast
          group
        calc c * (((na * nb : N) : G) * t * ((na * nb : N) : G)⁻¹) * c⁻¹ =
            (c * ((na * nb : N) : G)) * t * (c * ((na * nb : N) : G))⁻¹ := by group
          _ = t * z := by rw [this, hn']
      have hwC : (na : G)⁻¹ * c * na ∈ C := by
        have hna' : ((na⁻¹ : N) : G) ∈ Subgroup.normalizer (C : Set G) := by
          rw [hNC]
          exact (na⁻¹ : N).2
        have h := (Subgroup.mem_normalizer_iff.mp hna' c).mp hc
        simpa using h
      have hwna : ((na : G)⁻¹ * c * na * na) * t = t * ((na : G)⁻¹ * c * na * na) := by
        have h1 : (na : G) * t * (na : G)⁻¹ = t * z := hnat
        have h2 : ((na : G)⁻¹ * c * na) * (t * z) * ((na : G)⁻¹ * c * na)⁻¹ = t := by
          calc ((na : G)⁻¹ * c * na) * (t * z) * ((na : G)⁻¹ * c * na)⁻¹ =
              (na : G)⁻¹ * (c * ((na : G) * (t * z) * (na : G)⁻¹) * c⁻¹) * na := by group
            _ = (na : G)⁻¹ * ((na : G) * t * (na : G)⁻¹) * na := by rw [hcy]
            _ = t := by group
        calc ((na : G)⁻¹ * c * na * na) * t =
            ((na : G)⁻¹ * c * na) * ((na : G) * t * (na : G)⁻¹) * na := by group
          _ = ((na : G)⁻¹ * c * na) * (t * z) * ((na : G)⁻¹ * c * na)⁻¹ *
              (((na : G)⁻¹ * c * na) * na) := by rw [h1]; group
          _ = t * ((na : G)⁻¹ * c * na * na) := by rw [h2]
      have hwN : (na : G)⁻¹ * c * na ∈ N := hCN hwC
      have hmem := hmemC₀ (⟨(na : G)⁻¹ * c * na, hwN⟩ * na) (by simpa using hwna)
      rwa [map_mul, (hπker _).mpr hwC, one_mul, hna] at hmem
  obtain ⟨hC₀n, hC₀index⟩ := normal_index_le_two_of_mul_mem hmulC₀
  set Q : Subgroup G := Cg ⊓ N ⊓ Subgroup.centralizer ({t} : Set G) with hQdef
  have hTQ : T ≤ Q := fun y hy => ⟨⟨hTg hy, hTN hy⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (hTab y hy t htT)⟩
  have hQp : ∀ P : Subgroup G, P ≤ Q → IsPGroup 2 P → Nat.card P ≤ m :=
    fun P hPQ hP => (hmaxg P (hPQ.trans (inf_le_left.trans inf_le_left)) hP).2
  have hTQp : IsPGroup 2 (T.subgroupOf Q) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTQ).symm
  obtain ⟨PQ, hPQ⟩ := hTQp.exists_le_sylow
  have hPQeq : (PQ : Subgroup Q) = T.subgroupOf Q := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hPQ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, hTcard]
    have h := hQp ((PQ : Subgroup Q).map Q.subtype) (Subgroup.map_subtype_le _)
      (PQ.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)] at h
  have hPQcyc : IsCyclic (PQ : Subgroup Q) := by
    rw [hPQeq]
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTQ).injective
  obtain ⟨EQ, -, ⟨hEQodd, -⟩, -, -, hEQmem, hEQmul, -, -⟩ :=
    CFSG.Semidihedral.Principal.cyclicSylowTwo_normal_odd_complement PQ hPQcyc
  set EG : Subgroup G := EQ.map Q.subtype with hEGdef
  have hEGQ : EG ≤ Q := Subgroup.map_subtype_le _
  have hEGodd : ∀ y ∈ EG, Odd (orderOf y) := by
    rintro _ ⟨y, hy, rfl⟩
    have := (hEQmem y).mp hy
    show Odd (orderOf (y : G))
    rw [Subgroup.orderOf_coe]
    exact this
  have hQsplit : ∀ y ∈ Q, ∃ e ∈ EG, ∃ τ ∈ T, y = e * τ := by
    intro y hy
    have h : (⟨y, hy⟩ : Q) ∈ (EQ : Set Q) * (PQ : Set Q) := by rw [hEQmul]; trivial
    obtain ⟨e, he, p, hp, hep⟩ := Set.mem_mul.mp h
    have hp' : p ∈ T.subgroupOf Q := by rw [← hPQeq]; exact hp
    refine ⟨e, ⟨e, he, rfl⟩, p, Subgroup.mem_subgroupOf.mp hp', ?_⟩
    have := congrArg Subtype.val hep
    simpa using this.symm
  have hnQ : ∀ n : N, (n : G) * t = t * n → ∀ y ∈ Q, (n : G) * y * (n : G)⁻¹ ∈ Q := by
    intro n hn y hy
    have hyt : y ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hy).2
    have hyCg : y ∈ Cg := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1
    have hyN : y ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).2
    have hnCg : (n : G) ∈ Subgroup.normalizer (Cg : Set G) :=
      mem_normalizer_conj_of_commute hL (by rw [htord]; exact even_two) (hTg htT) hn
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hnCg y).mp hyCg,
        N.mul_mem (N.mul_mem n.2 hyN) (N.inv_mem n.2)⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyt ⊢
    have hn' : (n : G)⁻¹ * t = t * (n : G)⁻¹ := by
      calc (n : G)⁻¹ * t = (n : G)⁻¹ * (t * n) * (n : G)⁻¹ := by group
        _ = (n : G)⁻¹ * ((n : G) * t) * (n : G)⁻¹ := by rw [hn]
        _ = t * (n : G)⁻¹ := by group
    calc (n : G) * y * (n : G)⁻¹ * t = (n : G) * y * ((n : G)⁻¹ * t) := by group
      _ = (n : G) * (y * t) * (n : G)⁻¹ := by rw [hn']; group
      _ = (n : G) * (t * y) * (n : G)⁻¹ := by rw [hyt]
      _ = t * ((n : G) * y * (n : G)⁻¹) := by rw [← mul_assoc, hn]; group
  have hnEG : ∀ n : N, (n : G) * t = t * n → ∀ y ∈ EG, (n : G) * y * (n : G)⁻¹ ∈ EG := by
    intro n hn y hy
    have hyQ := hEGQ hy
    have hconjQ := hnQ n hn y hyQ
    refine ⟨⟨_, hconjQ⟩, (hEQmem _).mpr ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    have h := hEGodd y hy
    rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hEGN : EG ≤ N := hEGQ.trans (inf_le_left.trans inf_le_right)
  have hTNle : T ≤ N := hTN
  set Ebar : Subgroup (MulAut (L ⧸ Subgroup.center L)) := (EG.subgroupOf N).map π with hEbardef
  set Tbar : Subgroup (MulAut (L ⧸ Subgroup.center L)) := (T.subgroupOf N).map π with hTbardef
  have hEbarC₀ : Ebar ≤ C₀ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyQ := hEGQ (Subgroup.mem_subgroupOf.mp hy)
    exact hmemC₀ y (Subgroup.mem_centralizer_singleton_iff.mp hyQ.2)
  have hTbarC₀ : Tbar ≤ C₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmemC₀ y (hTab _ (Subgroup.mem_subgroupOf.mp hy) t htT)
  have hEbarodd : Odd (Nat.card Ebar) := by
    have h1 : Odd (Nat.card EG) := by
      rw [hEGdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)]
      exact hEQodd
    have h2 : Odd (Nat.card (EG.subgroupOf N)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGN).toEquiv]
    exact h2.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hTbarp : IsPGroup 2 Tbar :=
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTNle).symm).map π
  have hπT : ∀ y : N, (y : G) ∈ T → π y = 1 → (y : G) = 1 :=
    fun y hyT h => hTC y hyT ((hπker y).mp h)
  have huN : u ∈ N := hTN huT
  set uN : N := ⟨u, huN⟩ with huNdef
  have huN2 : uN ^ 2 = tN := Subtype.ext (by rw [Subgroup.coe_pow])
  have hπu2 : π uN ^ 2 = x := by rw [← map_pow, huN2]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    omega
  have huN4 : uN ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hu4]
    exact pow_orderOf_eq_one u)
  have hπu4 : orderOf (π uN) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := π uN)
      (by rw [pow_one, hπu2]; exact hx1)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, huN4, map_one])
    rw [h]
    norm_num
  have hsN : s ∈ N := hTN hsT
  have hTbarz : Tbar = Subgroup.zpowers (π ⟨s, hsN⟩) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hsTzp y (Subgroup.mem_subgroupOf.mp hy)
      have hyk : y = (⟨s, hsN⟩ : N) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [hyk, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ k
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hsT, rfl⟩
  have hTbarcyc : IsCyclic Tbar := by
    rw [hTbarz]
    exact Subgroup.isCyclic_zpowers _
  have hEbarCx : Ebar ≤ Cx := hEbarC₀.trans hC₀Cx
  have hTbarCx : Tbar ≤ Cx := hTbarC₀.trans hC₀Cx
  have hπuCx : π uN ∈ Cx := hmemCx uN (hTab u huT t htT)
  have hxCx : x ∈ Cx := hmemCx tN rfl
  have hxc : (⟨x, hxCx⟩ : Cx) ∈ Subgroup.center Cx := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w.2.2)
  have hEn : ∀ c ∈ C₀.subgroupOf Cx, ∀ e ∈ Ebar.subgroupOf Cx,
      c * e * c⁻¹ ∈ Ebar.subgroupOf Cx := by
    intro c hc e he
    rw [Subgroup.mem_subgroupOf] at hc he ⊢
    obtain ⟨n, hn, hnc⟩ := hc
    obtain ⟨y, hy, hye⟩ := he
    have hnt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hn)
    have hyEG := Subgroup.mem_subgroupOf.mp hy
    refine ⟨n * y * n⁻¹, Subgroup.mem_subgroupOf.mpr (hnEG n hnt y hyEG), ?_⟩
    rw [map_mul, map_mul, map_inv, hnc, hye]
    rfl
  have hconj : ∀ c ∈ C₀.subgroupOf Cx, ∃ e ∈ Ebar.subgroupOf Cx, ∃ τ ∈ Tbar.subgroupOf Cx,
      c * ⟨π uN, hπuCx⟩ * c⁻¹ = e * τ := by
    intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    obtain ⟨n, hn, hnc⟩ := hc
    have hnt := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨e, he, τ, hτ, hsplit⟩ := hQsplit _ (hnQ n hnt u (hTQ huT))
    have heN : e ∈ N := hEGN he
    have hτN : τ ∈ N := hTN hτ
    refine ⟨⟨π ⟨e, heN⟩, hEbarCx ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩,
      ⟨π ⟨τ, hτN⟩, hTbarCx ⟨⟨τ, hτN⟩, Subgroup.mem_subgroupOf.mpr hτ, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨⟨τ, hτN⟩, Subgroup.mem_subgroupOf.mpr hτ, rfl⟩, ?_⟩
    apply Subtype.ext
    have hsplit' : n * uN * n⁻¹ = (⟨e, heN⟩ : N) * ⟨τ, hτN⟩ := Subtype.ext hsplit
    change (c : MulAut (L ⧸ Subgroup.center L)) * π uN * (c : MulAut (L ⧸ Subgroup.center L))⁻¹ =
      π ⟨e, heN⟩ * π ⟨τ, hτN⟩
    rw [← hnc, ← map_inv, ← map_mul, ← map_mul, hsplit', map_mul]
  obtain ⟨B, hB, hBiso⟩ := exists_normal_four_quotient_oddCore (W := Cx) hC₀n hC₀index hxc
    (by rw [Subgroup.orderOf_mk]; exact hxord)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEbarCx).toEquiv])
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hEbarC₀ (Subgroup.mem_subgroupOf.mp hy))) hEn
    (hTbarp.of_equiv (Subgroup.subgroupOfEquivOfLe hTbarCx).symm)
    (fun y hy => Subgroup.mem_subgroupOf.mpr (hTbarC₀ (Subgroup.mem_subgroupOf.mp hy)))
    (isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hTbarCx).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTbarCx).injective)
    (u := ⟨π uN, hπuCx⟩) (Subgroup.mem_subgroupOf.mpr ⟨uN, Subgroup.mem_subgroupOf.mpr huT, rfl⟩)
    (by rw [Subgroup.orderOf_mk]; exact hπu4) (Subtype.ext (by rw [Subgroup.coe_pow]; exact hπu2))
    hconj
  exact hI M hInn x hxM hxord B hB hBiso

theorem standard_cyclic_centralizer_normal {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hO : CFSG.Assembly.oddCore G = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (hS : IsCyclic S)
    (hI : HypothesisOne (L ⧸ Subgroup.center L))
    (hsmall : (∀ g : G, g ∉ Subgroup.normalizer (L : Set G) → ∀ P : Subgroup G,
        P ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2) →
      ∀ g : G, g ∉ Subgroup.normalizer (L : Set G) →
        Odd (Nat.card ((Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.normalizer (L : Set G) : Subgroup G)))
    (h4 : 4 ≤ Nat.card S) : L.Normal := by
  by_cases hall : ∀ g : G, g ∉ Subgroup.normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2
  · exact normal_of_forall_odd_inf hL hO S hS (hsmall hall)
  · exfalso
    push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
      rw [hn] at hPcard ⊢
      have hn2 : 2 ≤ n := by
        by_contra h
        have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hL S hS hg (hP.trans inf_le_left) (hP.trans inf_le_right)
        hP2 hP4
    exact not_hypothesisOne_of_full_conj hL S hS h4 hg' hRC hR hRcard hTg hTN hT hTcard hRT hI

theorem card_sylow_eq_two_of_not_normal {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hO : CFSG.Assembly.oddCore G = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (hS : IsCyclic S)
    (hI : HypothesisOne (L ⧸ Subgroup.center L))
    (hsmall : (∀ g : G, g ∉ Subgroup.normalizer (L : Set G) → ∀ P : Subgroup G,
        P ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.normalizer (L : Set G) → IsPGroup 2 P → Nat.card P ≤ 2) →
      ∀ g : G, g ∉ Subgroup.normalizer (L : Set G) →
        Odd (Nat.card ((Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.normalizer (L : Set G) : Subgroup G)))
    (hnot : ¬ L.Normal) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : Nat.card S < 4 := by
    by_contra h
    exact hnot (standard_cyclic_centralizer_normal hL hO S hS hI hsmall (by omega))
  have heven : 2 ∣ Nat.card (Subgroup.centralizer (L : Set G)) := even_iff_two_dvd.mp hL.2.1
  have hpos : 0 < (Nat.card (Subgroup.centralizer (L : Set G))).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
  rw [Sylow.card_eq_multiplicity] at hlt ⊢
  set e := (Nat.card (Subgroup.centralizer (L : Set G))).factorization 2
  have he : e < 2 := by
    by_contra h
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he1 : e = 1 := by omega
  rw [he1, pow_one]

end CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
