module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import CFSG.FeitThompson.Definitions.SupportMultiplicity

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

def primeSupport (n : ℕ) : Set ℕ := {p : ℕ | p.Prime ∧ p ∣ n}

theorem mem_primeSupport_iff {n p : ℕ} : p ∈ primeSupport n ↔ p.Prime ∧ p ∣ n := Iff.rfl

theorem primeSupport_zero : primeSupport 0 = {p : ℕ | p.Prime} := by
  ext p; simp [mem_primeSupport_iff]

@[simp]
theorem primeSupport_one : primeSupport 1 = ∅ := by
  ext p
  simp only [mem_primeSupport_iff, Nat.dvd_one, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hp h => hp.one_lt.ne' h

theorem primeSupport_eq_coe_primeFactors {n : ℕ} (hn : n ≠ 0) :
    primeSupport n = (n.primeFactors : Set ℕ) := by
  ext p; simp [mem_primeSupport_iff, Nat.mem_primeFactors, hn]

theorem primeSupport_mono {m n : ℕ} (h : m ∣ n) : primeSupport m ⊆ primeSupport n :=
  fun _ hp => ⟨hp.1, hp.2.trans h⟩

theorem primeSupport_subset_setOf_prime (n : ℕ) : primeSupport n ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

theorem piCore_primeSupport_zero (X : Type*) [Group X] [Finite X] :
    piCore (primeSupport 0) X = ⊤ :=
  eq_top_iff.2 (le_piCore (Subgroup.normal_of_characteristic ⊤)
    (isPiSubgroup_iff.2 fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, dvd_zero p⟩))

variable [Finite G]

noncomputable def canonicalSignalizer (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G)
    (x : G) : Subgroup G :=
  (piCore (primeSupport (supportMultiplicity 𝓜 S x))
    (Subgroup.centralizer ({x} : Set G))).map (Subgroup.centralizer ({x} : Set G)).subtype

variable {𝓜 𝓝 : Set (Subgroup G)} {S T : Subgroup G → Subgroup G} {x : G}

theorem canonicalSignalizer_eq (𝓜 : Set (Subgroup G)) (S : Subgroup G → Subgroup G) (x : G) :
    canonicalSignalizer 𝓜 S x =
      (piCore (primeSupport (supportMultiplicity 𝓜 S x))
        (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype := (rfl)

theorem canonicalSignalizer_le_centralizer :
    canonicalSignalizer 𝓜 S x ≤ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.map_subtype_le _

theorem mul_comm_of_mem_canonicalSignalizer {g : G} (hg : g ∈ canonicalSignalizer 𝓜 S x) :
    g * x = x * g :=
  Subgroup.mem_centralizer_singleton_iff.1 (canonicalSignalizer_le_centralizer hg)

theorem mem_canonicalSignalizer_iff {g : G} :
    g ∈ canonicalSignalizer 𝓜 S x ↔ ∃ hg : g ∈ Subgroup.centralizer ({x} : Set G),
      (⟨g, hg⟩ : Subgroup.centralizer ({x} : Set G)) ∈
        piCore (primeSupport (supportMultiplicity 𝓜 S x))
          (Subgroup.centralizer ({x} : Set G)) := by
  rw [canonicalSignalizer_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩; exact ⟨⟨g, hg⟩, h, rfl⟩

theorem le_canonicalSignalizer {K : Subgroup (Subgroup.centralizer ({x} : Set G))}
    (hK : K.Normal) (hπ : IsPiSubgroup (primeSupport (supportMultiplicity 𝓜 S x)) K) :
    K.map (Subgroup.centralizer ({x} : Set G)).subtype ≤ canonicalSignalizer 𝓜 S x :=
  Subgroup.map_mono (le_piCore hK hπ)

theorem canonicalSignalizer_le_iff {H : Subgroup G} :
    canonicalSignalizer 𝓜 S x ≤ H ↔
      ∀ K : Subgroup (Subgroup.centralizer ({x} : Set G)), K.Normal →
        IsPiSubgroup (primeSupport (supportMultiplicity 𝓜 S x)) K →
        K.map (Subgroup.centralizer ({x} : Set G)).subtype ≤ H := by
  rw [canonicalSignalizer_eq, Subgroup.map_le_iff_le_comap, piCore_le_iff]
  exact forall_congr' fun K => by simp [Subgroup.map_le_iff_le_comap]

theorem canonicalSignalizer_eq_centralizer_of_supportMultiplicity_eq_zero
    (h : supportMultiplicity 𝓜 S x = 0) :
    canonicalSignalizer 𝓜 S x = Subgroup.centralizer ({x} : Set G) := by
  rw [canonicalSignalizer_eq, h, piCore_primeSupport_zero, ← MonoidHom.range_eq_map,
    Subgroup.subtype_range]

theorem canonicalSignalizer_eq_centralizer_of_forall_notMem (h : ∀ M ∈ 𝓜, x ∉ S M)
    (h𝓜 : 𝓜.Finite := by toFinite_tac) :
    canonicalSignalizer 𝓜 S x = Subgroup.centralizer ({x} : Set G) :=
  canonicalSignalizer_eq_centralizer_of_supportMultiplicity_eq_zero
    ((supportMultiplicity_eq_zero_iff h𝓜).2 h)

@[simp]
theorem canonicalSignalizer_empty (S : Subgroup G → Subgroup G) (x : G) :
    canonicalSignalizer (∅ : Set (Subgroup G)) S x = Subgroup.centralizer ({x} : Set G) :=
  canonicalSignalizer_eq_centralizer_of_supportMultiplicity_eq_zero
    (supportMultiplicity_empty S x)

theorem canonicalSignalizer_mono_of_dvd
    (h : supportMultiplicity 𝓜 S x ∣ supportMultiplicity 𝓝 T x) :
    canonicalSignalizer 𝓜 S x ≤ canonicalSignalizer 𝓝 T x :=
  Subgroup.map_mono (piCore_mono (primeSupport_mono h))

theorem canonicalSignalizer_congr (h : supportMultiplicity 𝓜 S x = supportMultiplicity 𝓝 T x) :
    canonicalSignalizer 𝓜 S x = canonicalSignalizer 𝓝 T x := by
  rw [canonicalSignalizer_eq, canonicalSignalizer_eq, h]

theorem canonicalSignalizer_one :
    canonicalSignalizer 𝓜 S 1 =
      (piCore (primeSupport 𝓜.ncard) (Subgroup.centralizer ({1} : Set G))).map
        (Subgroup.centralizer ({1} : Set G)).subtype := by
  rw [canonicalSignalizer_eq, supportMultiplicity_one]

end

end CFSG.FeitThompson
