module

public import Certificates.Data.Kernel.Misc.BfsKW
public import CFSG.Certificates.Kernel.Misc.BfsKSound

public section

namespace CFSG.KC.BfsKW

open CFSG.KD.BfsK CFSG.KD.BfsKW CFSG.KC.BfsK CFSG.Quasithin.G2U

theorem tableKW_ok {ok : List ℕ → Bool} {num : List ℕ → ℕ}
    (hinj : ∀ a b, ok a = true → ok b = true → num a = num b → a = b)
    {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {fuel o n k hiB hiS hiT : ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hst : ∀ x N, Enc ok num x N → ∀ s < k, ∀ d : List ℕ,
      Enc ok num (mul x (gens.getD s d)) (st N s))
    (h0 : Enc ok num start (recX R o 0))
    (h : tableKW R st o n k hiB hiS hiT = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * k ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    (build start mul gens (bfsParents start mul gens fuel)).size = n ∧
    closedCheck mul gens (build start mul gens (bfsParents start mul gens fuel)) = true ∧
    distinctCheck (build start mul gens (bfsParents start mul gens fuel)) = true ∧
    ∀ t < n, Enc ok num ((build start mul gens (bfsParents start mul gens fuel)).getD t [])
      (recX R o t) := by
  simp only [tableKW, Bool.and_eq_true] at h
  obtain ⟨⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, -, hsz, hcl, hdi, hrec⟩ :=
    tableE hinj hk hk0 hn hfuel hst h0 hB hBm hS hSm hT hTm
  rw [hpar]
  exact ⟨hsz, hcl, hdi, hrec⟩

end CFSG.KC.BfsKW

end
